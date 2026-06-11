# Core C Test Groups Summary

Command:

```bash
python demo/ci/run_core_test_groups.py --build-dir build-rel \
  --summary-json /tmp/timelog-storage-branchless-summary.json \
  --summary-md /tmp/timelog-storage-branchless-summary.md \
  --groups storage
```

Result:

- result: `pass`
- groups_total: `1`
- groups_passed: `1`
- groups_failed: `0`
- runner_os: `Linux`

| Group | Status | Exit Code | Duration (s) |
| --- | --- | --- | --- |
| `storage` | `pass` | `0` | `0.022535` |
