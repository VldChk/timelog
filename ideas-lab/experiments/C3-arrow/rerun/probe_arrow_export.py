#!/usr/bin/env python3
"""Rerun probe for C3-arrow.

Run with PYTHONPATH pointing at a build where C3-arrow/prototype.patch is applied.
Emits JSON with consumer support and pointer identity.
"""
from __future__ import annotations

import json

import numpy as np
import pyarrow as pa
import polars as pl
from timelog import Timelog


def main() -> None:
    log = Timelog(maintenance="disabled")
    for i in range(16):
        log.append(i, f"v{i}")
    log.flush()
    span = next(log.views(0, 16))

    memoryview_ptr = np.frombuffer(memoryview(span), dtype=np.int64).__array_interface__["data"][0]
    arrow_array = pa.array(span)
    arrow_ptr = arrow_array.buffers()[1].address
    polars_series = pl.Series("ts", span)

    close_error = None
    try:
        span.close()
    except Exception as exc:  # noqa: BLE001 - experiment records exact behavior.
        close_error = {"type": type(exc).__name__, "message": str(exc)}

    print(json.dumps({
        "pyarrow_version": pa.__version__,
        "polars_version": pl.__version__,
        "arrow_type": str(arrow_array.type),
        "arrow_values": arrow_array.to_pylist(),
        "memoryview_ptr": memoryview_ptr,
        "arrow_ptr": arrow_ptr,
        "arrow_pointer_identity": memoryview_ptr == arrow_ptr,
        "polars_dtype": str(polars_series.dtype),
        "polars_values": polars_series.to_list(),
        "close_while_arrow_live": close_error,
    }, sort_keys=True))

    del arrow_array, polars_series
    span.close()
    log.close()


if __name__ == "__main__":
    main()
