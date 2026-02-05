"""
Tests for API simplification: dict kwargs and preset constructors.

Tests the adaptive={...} and compaction={...} grouped dict kwargs,
preset classmethods (for_streaming, for_bulk_ingest, for_low_latency),
and backward compatibility of flat kwargs.
"""

import pytest
from timelog import Timelog


# =============================================================================
# Category 1: adaptive dict kwarg
# =============================================================================


class TestAdaptiveDict:
    """Test adaptive={...} grouped kwarg."""

    def test_adaptive_dict_basic(self):
        """adaptive dict with target_records enables adaptive mode."""
        with Timelog(adaptive={"target_records": 5000}) as log:
            log.append(1, "a")
            assert list(log) == [(1, "a")]

    def test_adaptive_dict_multiple_keys(self):
        """Multiple keys in adaptive dict are accepted."""
        with Timelog(adaptive={
            "target_records": 5000,
            "min_window": 100,
            "max_window": 100000,
            "alpha": 0.3,
        }) as log:
            log.append(1, "a")

    def test_adaptive_dict_all_keys(self):
        """All 10 adaptive keys are accepted."""
        with Timelog(adaptive={
            "target_records": 5000,
            "min_window": 100,
            "max_window": 100000,
            "hysteresis_pct": 10,
            "window_quantum": 1000,
            "alpha": 0.5,
            "warmup_flushes": 3,
            "stale_flushes": 10,
            "failure_backoff_threshold": 5,
            "failure_backoff_pct": 20,
        }) as log:
            log.append(1, "a")

    def test_adaptive_none_accepted(self):
        """adaptive=None is the same as omitting it."""
        with Timelog(adaptive=None) as log:
            log.append(1, "a")

    def test_adaptive_empty_dict(self):
        """Empty adaptive dict is valid (all defaults)."""
        with Timelog(adaptive={}) as log:
            log.append(1, "a")

    def test_adaptive_unknown_key_rejected(self):
        """Unknown key in adaptive dict raises ValueError."""
        with pytest.raises(ValueError, match="Unknown key.*bogus.*adaptive"):
            Timelog(adaptive={"bogus": 42})

    def test_adaptive_non_string_key_rejected(self):
        """Non-string keys in adaptive dict raise TypeError."""
        with pytest.raises(TypeError, match="adaptive keys must be str"):
            Timelog(adaptive={1: 2})

    def test_adaptive_not_dict_rejected(self):
        """Non-dict adaptive raises TypeError."""
        with pytest.raises(TypeError, match="adaptive must be a dict"):
            Timelog(adaptive="oops")

    def test_adaptive_not_dict_list_rejected(self):
        """List adaptive raises TypeError."""
        with pytest.raises(TypeError, match="adaptive must be a dict"):
            Timelog(adaptive=[1, 2, 3])

    def test_adaptive_conflict_raises(self):
        """Flat kwarg + same key in dict is an error."""
        with pytest.raises(ValueError, match="Cannot specify both"):
            Timelog(
                adaptive_target_records=5000,
                adaptive={"target_records": 5000},
            )

    def test_adaptive_flat_still_works(self):
        """Flat adaptive_* kwargs continue to work (backward compat)."""
        with Timelog(adaptive_target_records=5000) as log:
            log.append(1, "a")

    @pytest.mark.parametrize("val", [float("nan"), float("inf"), float("-inf")])
    def test_adaptive_alpha_non_finite_rejected_flat(self, val):
        """adaptive_alpha rejects NaN/Inf (flat kwarg)."""
        with pytest.raises(ValueError, match="adaptive_alpha must be finite"):
            Timelog(adaptive_alpha=val)

    @pytest.mark.parametrize("val", [float("nan"), float("inf"), float("-inf")])
    def test_adaptive_alpha_non_finite_rejected_dict(self, val):
        """adaptive alpha rejects NaN/Inf (dict kwarg)."""
        with pytest.raises(ValueError, match="adaptive_alpha must be finite"):
            Timelog(adaptive={"alpha": val})


# =============================================================================
# Category 2: compaction dict kwarg
# =============================================================================


class TestCompactionDict:
    """Test compaction={...} grouped kwarg."""

    def test_compaction_dict_basic(self):
        """compaction dict with target_bytes is accepted."""
        with Timelog(compaction={"target_bytes": 1048576}) as log:
            log.append(1, "a")

    def test_compaction_dict_all_keys(self):
        """All 3 compaction keys are accepted."""
        with Timelog(compaction={
            "target_bytes": 1048576,
            "max_inputs": 4,
            "max_windows": 8,
        }) as log:
            log.append(1, "a")

    def test_compaction_none_accepted(self):
        """compaction=None is accepted."""
        with Timelog(compaction=None) as log:
            log.append(1, "a")

    def test_compaction_empty_dict(self):
        """Empty compaction dict is valid."""
        with Timelog(compaction={}) as log:
            log.append(1, "a")

    def test_compaction_unknown_key_rejected(self):
        """Unknown key in compaction dict raises ValueError."""
        with pytest.raises(ValueError, match="Unknown key.*bogus.*compaction"):
            Timelog(compaction={"bogus": 42})

    def test_compaction_non_string_key_rejected(self):
        """Non-string keys in compaction dict raise TypeError."""
        with pytest.raises(TypeError, match="compaction keys must be str"):
            Timelog(compaction={1: 2})

    def test_compaction_not_dict_rejected(self):
        """Non-dict compaction raises TypeError."""
        with pytest.raises(TypeError, match="compaction must be a dict"):
            Timelog(compaction=123)

    def test_compaction_conflict_raises(self):
        """Flat kwarg + same key in dict is an error."""
        with pytest.raises(ValueError, match="Cannot specify both"):
            Timelog(
                compaction_target_bytes=1048576,
                compaction={"target_bytes": 1048576},
            )

    def test_compaction_flat_still_works(self):
        """Flat compaction kwargs continue to work."""
        with Timelog(compaction_target_bytes=1048576) as log:
            log.append(1, "a")


# =============================================================================
# Category 3: Both dicts together
# =============================================================================


class TestBothDicts:
    """Test using adaptive and compaction dicts simultaneously."""

    def test_both_dicts_together(self):
        """Both dict kwargs can be used at the same time."""
        with Timelog(
            adaptive={"target_records": 5000, "alpha": 0.3},
            compaction={"target_bytes": 1048576},
        ) as log:
            log.append(1, "a")

    def test_mixed_dict_and_flat(self):
        """Dict for one group, flat kwargs for the other."""
        with Timelog(
            adaptive={"target_records": 5000},
            compaction_target_bytes=1048576,
        ) as log:
            log.append(1, "a")


# =============================================================================
# Category 3b: Validation edge cases
# =============================================================================


class TestValidation:
    """Validate numeric edge cases and sentinel handling."""

    @pytest.mark.parametrize("val", [float("nan"), float("inf"), float("-inf")])
    def test_delete_debt_threshold_non_finite_rejected(self, val):
        """delete_debt_threshold rejects NaN/Inf."""
        with pytest.raises(ValueError, match="delete_debt_threshold must be finite"):
            Timelog(delete_debt_threshold=val)

    def test_memtable_max_bytes_negative_rejected(self):
        """Negative Py_ssize_t values are invalid (no -1 sentinel)."""
        with pytest.raises(ValueError, match="memtable_max_bytes must be >= 0"):
            Timelog(memtable_max_bytes=-1)

    def test_adaptive_target_records_negative_rejected_dict(self):
        """Adaptive target_records rejects negative values from dict."""
        with pytest.raises(ValueError, match="adaptive_target_records must be >= 0"):
            Timelog(adaptive={"target_records": -1})

# =============================================================================
# Category 4: Preset constructors
# =============================================================================


class TestPresets:
    """Test for_streaming, for_bulk_ingest, for_low_latency classmethods."""

    def test_for_streaming_creates_timelog(self):
        """for_streaming() returns a working Timelog."""
        with Timelog.for_streaming() as log:
            log.append(1, "a")
            log.append(2, "b")
            assert list(log) == [(1, "a"), (2, "b")]

    def test_for_streaming_with_overrides(self):
        """for_streaming() accepts overrides."""
        with Timelog.for_streaming(time_unit="us") as log:
            log.append(1, "a")

    def test_for_bulk_ingest_creates_timelog(self):
        """for_bulk_ingest() returns a working Timelog."""
        with Timelog.for_bulk_ingest() as log:
            for i in range(100):
                log.append(i, f"val_{i}")
            log.flush()
            assert len(list(log)) == 100

    def test_for_bulk_ingest_with_overrides(self):
        """for_bulk_ingest() accepts overrides."""
        with Timelog.for_bulk_ingest(time_unit="ns") as log:
            log.append(1, "a")

    def test_for_low_latency_creates_timelog(self):
        """for_low_latency() returns a working Timelog."""
        with Timelog.for_low_latency() as log:
            log.append(1, "a")
            assert list(log) == [(1, "a")]

    def test_for_low_latency_with_overrides(self):
        """for_low_latency() accepts overrides."""
        with Timelog.for_low_latency(time_unit="s") as log:
            log.append(1, "a")

    def test_preset_returns_timelog_instance(self):
        """All presets return Timelog (subclass) instances."""
        for factory in [Timelog.for_streaming, Timelog.for_bulk_ingest,
                        Timelog.for_low_latency]:
            with factory() as log:
                assert isinstance(log, Timelog)

    def test_preset_override_maintenance(self):
        """Presets allow overriding maintenance mode."""
        with Timelog.for_streaming(maintenance="disabled") as log:
            log.append(1, "a")

    def test_preset_with_dict_kwargs(self):
        """Presets accept dict kwargs too."""
        with Timelog.for_streaming(
            compaction={"target_bytes": 1048576}
        ) as log:
            log.append(1, "a")
