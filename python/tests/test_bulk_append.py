"""bulk_append(timestamps, objects) — typed-buffer ingest contract tests.

Covers: buffer formats and endianness policy, length/shape validation,
min_ts floor, mostly_ordered default resolution, EBUSY-means-committed,
all-or-nothing failure, lifecycle, and no-context-manager usage.
"""
import array
import sys

import pytest

from timelog import Timelog, TimelogBusyError

NATIVE_IS_LE = sys.byteorder == "little"


def _ts_array(values):
    return array.array("q", values)


class TestBulkAppendBasics:
    def test_roundtrip_array_array(self):
        log = Timelog(maintenance="disabled")
        log.bulk_append(_ts_array([10, 20, 30]), ["a", "b", "c"])
        assert list(log[0:100]) == [(10, "a"), (20, "b"), (30, "c")]
        log.close()

    def test_roundtrip_memoryview(self):
        log = Timelog(maintenance="disabled")
        log.bulk_append(memoryview(_ts_array([1, 2])), ("x", "y"))
        assert list(log[0:10]) == [(1, "x"), (2, "y")]
        log.close()

    def test_empty_is_noop(self):
        log = Timelog(maintenance="disabled")
        log.bulk_append(_ts_array([]), [])
        assert len(log) == 0
        log.close()

    def test_duplicate_timestamps_kept(self):
        log = Timelog(maintenance="disabled")
        log.bulk_append(_ts_array([5, 5, 5]), [1, 2, 3])
        assert sorted(log[5]) == [1, 2, 3]
        log.close()

    def test_unsorted_input_ok(self):
        log = Timelog(maintenance="disabled")
        log.bulk_append(_ts_array([30, 10, 20]), ["c", "a", "b"])
        assert list(log[0:100]) == [(10, "a"), (20, "b"), (30, "c")]
        log.close()

    def test_no_context_manager_no_close(self):
        # The 99.9999% case: plain usage, abandoned to GC.
        log = Timelog(maintenance="disabled")
        log.bulk_append(_ts_array(range(1000)), list(range(1000)))
        assert len(log) == 1000
        del log  # finalizer must clean up without errors


class TestBulkAppendNumpy:
    np = pytest.importorskip("numpy")

    def test_native_int64(self):
        np = self.np
        log = Timelog(maintenance="disabled")
        log.bulk_append(np.array([1, 2, 3], dtype=np.int64), ["a", "b", "c"])
        assert list(log[0:10]) == [(1, "a"), (2, "b"), (3, "c")]
        log.close()

    def test_byteswapped_rejected(self):
        np = self.np
        log = Timelog(maintenance="disabled")
        swapped = np.array([1, 2], dtype=np.int64).byteswap().view(
            np.dtype(np.int64).newbyteorder())
        with pytest.raises(ValueError, match="endian|byte order|native"):
            log.bulk_append(swapped, ["a", "b"])
        assert len(log) == 0  # nothing inserted
        log.close()

    def test_float64_rejected(self):
        np = self.np
        log = Timelog(maintenance="disabled")
        with pytest.raises((ValueError, TypeError)):
            log.bulk_append(np.array([1.0, 2.0]), ["a", "b"])
        log.close()

    def test_int32_rejected(self):
        np = self.np
        log = Timelog(maintenance="disabled")
        with pytest.raises(ValueError, match="8-byte|int64"):
            log.bulk_append(np.array([1, 2], dtype=np.int32), ["a", "b"])
        log.close()

    def test_2d_rejected(self):
        np = self.np
        log = Timelog(maintenance="disabled")
        with pytest.raises(ValueError, match="1-D"):
            log.bulk_append(np.zeros((2, 2), dtype=np.int64), ["a", "b"])
        log.close()

    def test_noncontiguous_rejected(self):
        np = self.np
        log = Timelog(maintenance="disabled")
        strided = np.arange(10, dtype=np.int64)[::2]
        with pytest.raises((ValueError, BufferError)):
            log.bulk_append(strided, list(range(5)))
        log.close()


class TestBulkAppendValidation:
    def test_length_mismatch(self):
        log = Timelog(maintenance="disabled")
        with pytest.raises(ValueError, match="length mismatch"):
            log.bulk_append(_ts_array([1, 2, 3]), ["a", "b"])
        assert len(log) == 0
        log.close()

    def test_non_buffer_timestamps(self):
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError):
            log.bulk_append([1, 2, 3], ["a", "b", "c"])  # list is not a buffer
        log.close()

    def test_bytearray_timestamps_rejected(self):
        # itemsize=1 buffer must be rejected by the itemsize check.
        log = Timelog(maintenance="disabled")
        with pytest.raises(ValueError, match="8-byte|int64"):
            log.bulk_append(bytearray(b"\x00" * 8), ["a"])
        log.close()

    def test_misaligned_buffer_rejected(self):
        # A sliced byte-buffer cast passes the itemsize/format checks but its
        # data pointer is misaligned: reading it as int64_t* would be UB.
        log = Timelog(maintenance="disabled")
        misaligned = memoryview(bytearray(17))[1:9].cast("q")
        assert misaligned.format == "q" and misaligned.itemsize == 8
        with pytest.raises(ValueError, match="aligned"):
            log.bulk_append(misaligned, ["x"])
        assert len(log) == 0
        # The aligned slice of the same buffer is accepted.
        aligned = memoryview(bytearray(16))[0:8].cast("q")
        log.bulk_append(aligned, ["ok"])
        assert len(log) == 1
        log.close()

    def test_generator_objects_rejected(self):
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError, match="sequence"):
            log.bulk_append(_ts_array([1]), (x for x in "a"))
        log.close()

    def test_string_objects_rejected(self):
        # 'abc' would otherwise silently insert 3 character records.
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError, match="str|bytes"):
            log.bulk_append(_ts_array([1, 2, 3]), "abc")
        assert len(log) == 0
        log.close()

    def test_set_objects_rejected(self):
        # Unordered containers cannot be a parallel array.
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError, match="sequence"):
            log.bulk_append(_ts_array([1, 2]), {"a", "b"})
        log.close()

    def test_all_or_nothing_on_invalid_ts(self):
        # min_ts floor violation mid-batch must insert NOTHING.
        log = Timelog(maintenance="disabled", min_ts=100)
        with pytest.raises(ValueError):
            log.bulk_append(_ts_array([150, 50, 200]), ["a", "b", "c"])
        assert len(log) == 0
        log.close()

    def test_floor_violation_at_index_zero(self):
        log = Timelog(maintenance="disabled", min_ts=100)
        with pytest.raises(ValueError):
            log.bulk_append(_ts_array([99, 150]), ["x", "y"])
        assert len(log) == 0
        log.close()

    def test_min_ts_floor_enforced(self):
        log = Timelog(maintenance="disabled", min_ts=1000)
        with pytest.raises(ValueError):
            log.bulk_append(_ts_array([999]), ["x"])
        log.bulk_append(_ts_array([1000]), ["ok"])
        assert log[1000] == ["ok"]
        log.close()

    def test_closed_raises(self):
        from timelog import TimelogError
        log = Timelog(maintenance="disabled")
        log.close()
        with pytest.raises(TimelogError):
            log.bulk_append(_ts_array([1]), ["a"])

    def test_kwargs_contract(self):
        # Hand-rolled FASTCALL parser: kw form, unknown kw, duplicate, missing.
        log = Timelog(maintenance="disabled")
        log.bulk_append(timestamps=_ts_array([1]), objects=["a"])
        with pytest.raises(TypeError, match="unexpected keyword"):
            log.bulk_append(_ts_array([2]), ["b"], wrong_kw=1)
        with pytest.raises(TypeError, match="multiple values"):
            log.bulk_append(_ts_array([3]), ["c"], objects=["d"])
        with pytest.raises(TypeError):
            log.bulk_append(_ts_array([4]))  # missing objects
        with pytest.raises(TypeError):
            log.bulk_append(_ts_array([5]), ["e"], ["extra"], None)  # too many positional
        assert len(log) == 1
        log.close()


class TestBulkAppendSemantics:
    def test_mostly_ordered_default_resolution(self):
        # mostly_ordered=None (default) resolves to the instance default, like extend().
        log = Timelog(maintenance="disabled", mostly_ordered_default=True)
        log.bulk_append(_ts_array([1, 2, 3]), ["a", "b", "c"])  # must not raise
        log2 = Timelog(maintenance="disabled", mostly_ordered_default=False)
        log2.bulk_append(_ts_array([3, 1, 2]), ["c", "a", "b"])
        assert list(log2[0:10]) == [(1, "a"), (2, "b"), (3, "c")]
        log.close()
        log2.close()

    def test_mostly_ordered_explicit_overrides_default(self):
        log = Timelog(maintenance="disabled", mostly_ordered_default=True)
        log.bulk_append(_ts_array([3, 1, 2]), ["c", "a", "b"], mostly_ordered=False)
        log.bulk_append(_ts_array([4, 5, 6]), ["d", "e", "f"], mostly_ordered=True)
        assert list(log[0:10]) == [
            (1, "a"), (2, "b"), (3, "c"), (4, "d"), (5, "e"), (6, "f")]
        log.close()

    def test_ebusy_raised_and_all_committed(self):
        # Deterministic backpressure: manual mode, 1-slot sealed queue, no wait,
        # tiny memtable. Each 1000-record batch (16 KB) overflows the 4 KiB
        # memtable: batch 1 seals into the empty queue; batch 2's seal finds the
        # queue full -> TL_EBUSY -> TimelogBusyError (busy_policy='raise').
        log = Timelog(maintenance="disabled", busy_policy="raise",
                      memtable_max_bytes=4096, sealed_max_runs=1, sealed_wait_ms=0)
        raised = False
        for batch in range(2):
            ts = _ts_array(range(batch * 1000, batch * 1000 + 1000))
            try:
                log.bulk_append(ts, list(range(batch * 1000, batch * 1000 + 1000)))
            except TimelogBusyError:
                raised = True   # records ARE committed
        assert raised, "backpressure construction failed to trigger TimelogBusyError"
        log.flush()
        assert len(log) == 2000     # every record present exactly once, none lost
        log.close()

    def test_busy_policy_flush_and_silent_swallow_ebusy(self):
        for policy in ("flush", "silent"):
            log = Timelog(maintenance="disabled", busy_policy=policy,
                          memtable_max_bytes=4096, sealed_max_runs=1,
                          sealed_wait_ms=0)
            for batch in range(2):
                log.bulk_append(
                    _ts_array(range(batch * 1000, batch * 1000 + 1000)),
                    list(range(1000)))   # must NOT raise
            log.flush()
            assert len(log) == 2000
            log.close()

    def test_interleave_with_append_and_delete(self):
        log = Timelog(maintenance="disabled")
        log.append("early", ts=5)
        log.bulk_append(_ts_array([10, 20]), ["a", "b"])
        del log[10:15]
        log.bulk_append(_ts_array([10]), ["a2"])
        assert list(log[0:100]) == [(5, "early"), (10, "a2"), (20, "b")]
        log.close()

    def test_bulk_append_after_flush_and_compact(self):
        log = Timelog(maintenance="disabled")
        log.bulk_append(_ts_array(range(100)), list(range(100)))
        log.flush()
        log.compact()
        log.maint_step()
        log.bulk_append(_ts_array(range(100, 200)), list(range(100, 200)))
        assert len(log) == 200
        log.close()

    def test_bulk_append_with_open_iterator_and_view(self):
        # Snapshot isolation: pre-existing readers must not see the new batch.
        log = Timelog(maintenance="disabled")
        log.bulk_append(_ts_array([1, 2]), ["a", "b"])
        log.flush()
        it = log.range(0, 1000)
        spans = log.views()
        log.bulk_append(_ts_array([3]), ["c"])
        assert [ts for ts, _ in it] == [1, 2]   # iterator sees its snapshot only
        spans.close()
        assert log[3] == ["c"]                  # new reader sees the new record
        log.close()

    def test_source_list_mutation_after_call_is_isolated(self):
        # The C layer snapshots the objects sequence; later mutation of the
        # caller's list must not affect stored payloads.
        log = Timelog(maintenance="disabled")
        payloads = ["a", "b"]
        log.bulk_append(_ts_array([1, 2]), payloads)
        payloads[0] = "MUTATED"
        payloads.clear()
        assert list(log[0:10]) == [(1, "a"), (2, "b")]
        log.close()

    def test_objects_kept_alive_and_released(self):
        import gc
        import weakref

        class Payload:
            pass

        log = Timelog(maintenance="disabled")
        p = Payload()
        ref = weakref.ref(p)
        log.bulk_append(_ts_array([1]), [p])
        del p
        gc.collect()
        assert ref() is not None       # log holds a reference
        log.close()
        gc.collect()
        assert ref() is None           # close releases tracked refs

    def test_abandoned_log_releases_objects(self):
        # No-context-manager abandonment: finalizer must release tracked refs.
        import gc
        import weakref

        class Payload:
            pass

        log = Timelog(maintenance="disabled")
        p = Payload()
        ref = weakref.ref(p)
        log.bulk_append(_ts_array([1]), [p])
        del p
        del log                        # abandon WITHOUT close()
        for _ in range(3):
            gc.collect()               # robust under 3.14t deferred refcounting
        assert ref() is None, "abandoned Timelog leaked a payload reference"
