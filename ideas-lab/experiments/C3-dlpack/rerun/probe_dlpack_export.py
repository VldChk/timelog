#!/usr/bin/env python3
"""Rerun probe for C3-dlpack.

Run with PYTHONPATH pointing at a build where C3-dlpack/prototype.patch is applied.
Emits JSON with NumPy DLPack support, pointer identity, and read-only behavior.
"""
from __future__ import annotations

import json

import numpy as np
from timelog import Timelog


def main() -> None:
    log = Timelog(maintenance="disabled")
    for i in range(16):
        log.append(i, f"v{i}")
    log.flush()
    span = next(log.views(0, 16))

    mv_arr = np.frombuffer(memoryview(span), dtype=np.int64)
    dl_arr = np.from_dlpack(span)

    write_error = None
    try:
        dl_arr[0] = 999
    except Exception as exc:  # noqa: BLE001 - experiment records exact behavior.
        write_error = {"type": type(exc).__name__, "message": str(exc)}

    print(json.dumps({
        "numpy_version": np.__version__,
        "dlpack_device": span.__dlpack_device__(),
        "memoryview_ptr": int(mv_arr.__array_interface__["data"][0]),
        "dlpack_ptr": int(dl_arr.__array_interface__["data"][0]),
        "dlpack_pointer_identity": int(mv_arr.__array_interface__["data"][0]) == int(dl_arr.__array_interface__["data"][0]),
        "dlpack_dtype": str(dl_arr.dtype),
        "dlpack_values": dl_arr.tolist(),
        "dlpack_writeable": bool(dl_arr.flags.writeable),
        "write_error": write_error,
    }, sort_keys=True))

    span.close()
    log.close()


if __name__ == "__main__":
    main()
