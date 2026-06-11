# Timelog Resilience Lab — Report

- Engine version: `1.2.0`
- Python: `3.13.12` (Py_GIL_DISABLED=0)
- Platform: `Linux-6.17.0-29-generic-x86_64-with-glibc2.39`
- Scenarios: **112/112 passed**, 0 failed
- Total verified cases (incl. property + config + churn iterations): **2858**
- Wall time: 63.5s

## Results by domain

| Domain | Passed | Cases | Wall (s) |
|---|---|---|---|
| analytics | 5/5 | 5 | 10.6 |
| asyncio | 4/4 | 4 | 1.2 |
| backend_extra | 4/4 | 4 | 0.4 |
| cache_ttl | 6/6 | 39 | 0.4 |
| concurrency | 6/6 | 6 | 0.7 |
| config_matrix | 16/16 | 96 | 0.5 |
| distributed | 6/6 | 22 | 1.2 |
| edge | 10/10 | 24 | 0.3 |
| event_sourcing | 6/6 | 15 | 5.3 |
| hft | 6/6 | 17 | 5.0 |
| iot | 6/6 | 13 | 25.0 |
| lifecycle | 7/7 | 511 | 0.2 |
| lifecycle_concurrent | 8/8 | 85 | 2.0 |
| observability | 6/6 | 6 | 1.6 |
| product | 8/8 | 8 | 0.6 |
| property | 5/5 | 2000 | 5.0 |
| rate_limit | 3/3 | 3 | 3.4 |

## Verdict

All scenarios passed. Every mutation was mirrored to a naive reference oracle and every query (range / since / until / point / at / all / len / min_ts / max_ts) matched it exactly on the timestamp sequence and per-timestamp payload multiset, with sortedness and tombstone-leak invariants enforced throughout.

## Scenario inventory

**analytics**
- [ok] tumbling_windows_partition_complete (cases=1)
- [ok] sliding_windows_monotone_counts (cases=1)
- [ok] downsample_bucket_sums (cases=1)
- [ok] rolling_retention_window (cases=1)
- [ok] since_until_equivalence (cases=1)

**asyncio**
- [ok] cooperative_producers_consumers (cases=1)
- [ok] to_thread_concurrent_appends (cases=1)
- [ok] async_ttl_cache (cases=1)
- [ok] gather_concurrent_reads (cases=1)

**backend_extra**
- [ok] circuit_breaker_sliding_failure_windows (cases=1)
- [ok] dsa_interval_sweep_resource_load (cases=1)
- [ok] web_request_log_processing (cases=1)
- [ok] non_context_manager_auto_close_lifetime (cases=1)

**cache_ttl**
- [ok] sliding_window_eviction (cases=1)
- [ok] reinsert_into_evicted_range (cases=1)
- [ok] ttl_window_count_accuracy (cases=1)
- [ok] burst_idle_evict_cycles (cases=15)
- [ok] overlapping_evictions (cases=1)
- [ok] random_ttl_workload (cases=20)

**concurrency**
- [ok] concurrent_appends_distinct_ranges (cases=1)
- [ok] concurrent_appends_overlapping_ts (cases=1)
- [ok] readers_vs_writer_snapshot_consistency (cases=1)
- [ok] readers_vs_deleter_no_crash (cases=1)
- [ok] close_during_concurrent_mutation (cases=1)
- [ok] many_concurrent_iterators (cases=1)

**config_matrix**
- [ok] maint_disabled (cases=6)
- [ok] maint_background (cases=6)
- [ok] busy_raise (cases=6)
- [ok] busy_silent (cases=6)
- [ok] busy_flush (cases=6)
- [ok] tiny_memtable (cases=6)
- [ok] small_memtable (cases=6)
- [ok] tiny_pages (cases=6)
- [ok] sealed_runs_1 (cases=6)
- [ok] sealed_runs_8 (cases=6)
- [ok] mostly_ordered_on (cases=6)
- [ok] mostly_ordered_off (cases=6)
- [ok] bg_tiny_memtable (cases=6)
- [ok] bg_busy_flush (cases=6)
- [ok] for_bulk_ingest_like (cases=6)
- [ok] for_streaming_like (cases=6)

**distributed**
- [ok] multi_node_clock_skew_merge (cases=10)
- [ok] late_arrival_into_processed_window (cases=1)
- [ok] at_least_once_duplicates_preserved (cases=8)
- [ok] partition_replay_interleave (cases=1)
- [ok] tombstone_then_late_event_survives (cases=1)
- [ok] dedup_last_write_wins_pattern (cases=1)

**edge**
- [ok] extreme_timestamp_boundaries (cases=1)
- [ok] empty_ranges_are_noops (cases=1)
- [ok] inverted_ranges_raise (cases=1)
- [ok] single_record (cases=1)
- [ok] all_identical_timestamp_mass_ties (cases=1)
- [ok] fully_reversed_ingestion (cases=1)
- [ok] overlapping_and_adjacent_tombstones (cases=1)
- [ok] delete_everything_then_rebuild (cases=1)
- [ok] delete_reinsert_churn (cases=15)
- [ok] huge_gaps_sparse (cases=1)

**event_sourcing**
- [ok] append_only_full_replay (cases=1)
- [ok] snapshot_isolation_under_mutation (cases=1)
- [ok] compaction_preserves_all_data (cases=10)
- [ok] audit_trail_point_in_time (cases=1)
- [ok] metrics_last_value_and_retention (cases=1)
- [ok] alert_threshold_scan (cases=1)

**hft**
- [ok] monotonic_tick_stream_range_scans (cases=1)
- [ok] out_of_order_ticks_jitter (cases=10)
- [ok] vwap_window_value_correctness (cases=1)
- [ok] point_in_time_book_reconstruction (cases=1)
- [ok] backpressure_busy_policy_no_loss (cases=3)
- [ok] l2_updates_dense_same_ts (cases=1)

**iot**
- [ok] multi_device_periodic_telemetry (cases=8)
- [ok] backfill_then_live_tail (cases=1)
- [ok] high_cardinality_devices_window_filter (cases=1)
- [ok] late_sensor_into_retained_window (cases=1)
- [ok] rolling_retention_high_rate (cases=1)
- [ok] sparse_gappy_signal (cases=1)

**lifecycle**
- [ok] context_manager_closes (cases=1)
- [ok] double_close_is_safe (cases=1)
- [ok] close_refused_with_active_iterator (cases=1)
- [ok] gc_collects_unclosed (cases=1)
- [ok] reopen_starts_fresh (cases=1)
- [ok] many_short_lived_logs (cases=500)
- [ok] interleaved_open_logs (cases=6)

**lifecycle_concurrent**
- [ok] close_vs_iter_pin_three_thread (cases=20)
- [ok] pagespan_mv_close_three_thread (cases=15)
- [ok] gc_during_heavy_mutation (cases=5)
- [ok] concurrent_reopen_raises_cleanly (cases=25)
- [ok] maintenance_toggle_during_writes (cases=1)
- [ok] subinterpreter_shutdown_unclosed (cases=1)
- [ok] worker_on_drop_no_leaks (cases=10)
- [ok] asyncio_to_thread_close (cases=8)

**observability**
- [ok] structured_log_severity_filter (cases=1)
- [ok] log_tail_pagination_no_dup_or_skip (cases=1)
- [ok] distributed_trace_spans (cases=1)
- [ok] metrics_scrape_windows (cases=1)
- [ok] log_rotation_retention (cases=1)
- [ok] error_burst_detection (cases=1)

**product**
- [ok] ohlcv_candle_aggregation (cases=1)
- [ok] leaderboard_time_decay_window (cases=1)
- [ok] feature_flag_point_in_time (cases=1)
- [ok] chat_timeline_pagination (cases=1)
- [ok] ab_test_event_funnel (cases=1)
- [ok] zerocopy_pagespan_value_fidelity (cases=1)
- [ok] zerocopy_numpy_timestamps (cases=1)
- [ok] views_physical_vs_logical_contract (cases=1)

**property**
- [ok] full_differential_disabled (cases=500)
- [ok] full_differential_background (cases=400)
- [ok] clustered_ties_heavy (cases=400)
- [ok] boundary_timestamps (cases=400)
- [ok] wide_domain (cases=300)

**rate_limit**
- [ok] sliding_window_counter_accuracy (cases=1)
- [ok] windowed_with_pruning (cases=1)
- [ok] per_key_quota_scan (cases=1)
