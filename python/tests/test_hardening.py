"""Hardening regression guards (idea 5).

Each test pins a safety property that ALREADY holds today, so it passes on first
run and fails only if a future change regresses the property:

1. The binding heap types wire no ``tp_call`` / vectorcall slot (instances are
   not callable). The load-bearing probe is the ``Py_TPFLAGS_HAVE_VECTORCALL``
   flag bit, NOT ``callable()`` alone -- ``callable()`` reads only ``tp_call``
   and would miss a half-wired ``tp_vectorcall_offset``.
2. PageSpan is the SOLE buffer exporter, and it exports only the read-only
   int64 timestamp array. The encoded handle array (``h[]``, raw ``PyObject*``)
   is never exposed as numeric zero-copy data -- doing so would disclose/forge
   pointers (UAF). Decoded objects are reachable only as real Python objects.
3. PageSpan satisfies the PEP 688 buffer protocol (``collections.abc.Buffer``).
"""
from __future__ import annotations

import collections.abc

import pytest

import timelog
from timelog import _timelog

# Py_TPFLAGS_HAVE_VECTORCALL (Include/object.h). The binding must never set it.
_HAVE_VECTORCALL = 1 << 11

# The binding heap types whose call/buffer surface we pin (raw C types, so the
# invariant is the binding's, independent of any facade subclassing).
_C_TYPES = (
    _timelog.Timelog,
    _timelog.TimelogIter,
    _timelog.PageSpan,
    _timelog.PageSpanIter,
    _timelog.PageSpanObjectsView,
)


def _make_span(values=("v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7")):
    """Return (log, span) with `len(values)` records materialized into a page."""
    log = timelog.Timelog(maintenance="disabled")
    log.extend([(i, v) for i, v in enumerate(values)])
    log.flush()
    span = next(log.views(0, len(values)))
    return log, span


class TestNoVectorcall:
    def test_binding_types_lack_have_vectorcall_flag(self):
        # Load-bearing: HAVE_VECTORCALL must stay clear on every binding type.
        for T in _C_TYPES:
            assert not (T.__flags__ & _HAVE_VECTORCALL), (
                f"{T.__name__} grew Py_TPFLAGS_HAVE_VECTORCALL -- a tp_vectorcall"
                " slot was wired on a binding heap type"
            )

    def test_instances_not_callable(self):
        # Secondary (weaker) check: nothing the binding exposes is callable.
        # (A type is always callable -- that is construction. We pin that
        # INSTANCES are not callable, i.e. no tp_call/vectorcall on the type.)
        log, span = _make_span()
        try:
            assert not callable(log)
            assert not callable(span)
        finally:
            span.close()
            log.close()


class TestBufferSurface:
    def test_pagespan_is_sole_buffer_exporter(self):
        # Structural guard: if any other binding type grows a buffer slot, this
        # trips. PEP 688's subclasshook recognizes the C bf_getbuffer slot.
        buffer_types = {T for T in _C_TYPES if issubclass(T, collections.abc.Buffer)}
        assert buffer_types == {_timelog.PageSpan}

    def test_buffer_is_readonly_int64_timestamps(self):
        log, span = _make_span()
        mv = memoryview(span)
        try:
            assert mv.readonly is True
            assert mv.ndim == 1
            assert mv.format == "q"          # hardcoded PAGESPAN_TS_FORMAT
            assert mv.itemsize == 8          # int64
            assert mv.nbytes == len(span) * 8
            assert mv.tolist() == list(range(len(span)))   # timestamps 0..len-1
        finally:
            mv.release()
            span.close()
            log.close()

    def test_buffer_rejects_writes(self):
        # Read-only export -> any write must raise (the getbuffer also refuses a
        # PyBUF_WRITABLE request with BufferError at the C level; from Python the
        # observable guarantee is read-only + write rejection).
        log, span = _make_span()
        mv = memoryview(span)
        try:
            assert mv.readonly is True
            with pytest.raises((TypeError, ValueError)):
                mv[0] = 999
            # Reinterpret as bytes (q->B is allowed) and confirm the write is
            # still refused -- read-only propagates through cast.
            with pytest.raises((TypeError, ValueError)):
                mv.cast("B")[0] = 1
        finally:
            mv.release()
            span.close()
            log.close()

    def test_handles_never_exported_as_numeric(self):
        # The decoded objects view yields the ORIGINAL Python objects, never the
        # raw uint64 handle, and is not itself a numeric buffer.
        log, span = _make_span(values=("a", "b", "c", "d"))
        try:
            objs = list(span.objects())
            assert objs == ["a", "b", "c", "d"]
            assert not isinstance(span.objects(), collections.abc.Buffer)
            with pytest.raises(TypeError):
                memoryview(span.objects())
        finally:
            span.close()
            log.close()


class TestPep688Buffer:
    def test_pagespan_is_collections_abc_buffer(self):
        log, span = _make_span()
        try:
            assert isinstance(span, collections.abc.Buffer)
            # memoryview() must succeed on a PEP 688 Buffer.
            mv = memoryview(span)
            mv.release()
        finally:
            span.close()
            log.close()
