"""Compatibility-baseline tests for isolated subinterpreters."""

from __future__ import annotations

import pytest


pytestmark = [pytest.mark.subinterpreters]

_LAYER_A_XFAIL_REASON = (
    "Layer A is not implemented yet: timelog still relies on process-global "
    "Python objects and static extension types."
)


def _maybe_xfail_known_layer_a_failure(payload):
    kind, exc_type, message = payload
    assert kind == "error"

    message_lower = message.lower()
    if exc_type == "ImportError" and "does not support loading in subinterpreters" in message_lower:
        pytest.xfail(_LAYER_A_XFAIL_REASON)
    if exc_type == "RuntimeError" and "subinterpreter" in message_lower:
        pytest.xfail(_LAYER_A_XFAIL_REASON)

    raise AssertionError(f"unexpected subinterpreter failure: {exc_type}: {message}")


def test_subinterpreter_smoke_roundtrip(compat_runtime, compat_package_root):
    interpreters = compat_runtime.require_subinterpreters()

    result_queue = interpreters.create_queue()
    interp = interpreters.create()
    try:
        interp.prepare_main(
            package_root=compat_package_root,
            result_queue=result_queue,
        )
        try:
            interp.exec(
                """
                import sys

                sys.path.insert(0, package_root)

                try:
                    from timelog import Timelog

                    with Timelog() as log:
                        log.append(1, "alpha")
                        log.append(2, "beta")
                        rows = tuple(log[1:3])

                    result_queue.put(("ok", rows))
                except Exception as exc:
                    result_queue.put(("error", type(exc).__name__, str(exc)))
                """
            )
        except interpreters.ExecutionFailed as exc:
            raise AssertionError(f"unexpected interpreter execution failure: {exc}") from exc

        payload = result_queue.get(timeout=5.0)
        if payload[0] == "error":
            _maybe_xfail_known_layer_a_failure(payload)

        rows = payload[1]
        assert tuple(rows) == ((1, "alpha"), (2, "beta"))
    finally:
        interp.close()


def test_subinterpreter_identities_are_isolated(compat_runtime, compat_package_root):
    interpreters = compat_runtime.require_subinterpreters()

    left_queue = interpreters.create_queue()
    right_queue = interpreters.create_queue()
    left_interp = interpreters.create()
    right_interp = interpreters.create()

    try:
        for interp, queue in ((left_interp, left_queue), (right_interp, right_queue)):
            interp.prepare_main(
                package_root=compat_package_root,
                result_queue=queue,
            )
            try:
                interp.exec(
                    """
                    import sys

                    sys.path.insert(0, package_root)

                    try:
                        import timelog._timelog as c_timelog

                        result_queue.put(
                            (
                                "ok",
                                (
                                    id(c_timelog.TimelogError),
                                    id(c_timelog.Timelog),
                                    id(c_timelog.PageSpan),
                                ),
                            )
                        )
                    except Exception as exc:
                        result_queue.put(("error", type(exc).__name__, str(exc)))
                    """
                )
            except interpreters.ExecutionFailed as exc:
                raise AssertionError(f"unexpected interpreter execution failure: {exc}") from exc

        left_payload = left_queue.get(timeout=5.0)
        right_payload = right_queue.get(timeout=5.0)
        if left_payload[0] == "error":
            _maybe_xfail_known_layer_a_failure(left_payload)
        if right_payload[0] == "error":
            _maybe_xfail_known_layer_a_failure(right_payload)

        left_ids = left_payload[1]
        right_ids = right_payload[1]

        assert left_ids[0] != right_ids[0]
        assert left_ids[1] != right_ids[1]
        assert left_ids[2] != right_ids[2]
    finally:
        left_interp.close()
        right_interp.close()
