"""Compatibility-baseline tests for isolated subinterpreters."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import json
import os
import subprocess
import sys
from textwrap import dedent

import pytest


pytestmark = [pytest.mark.subinterpreters]


def _exec(interp, code: str) -> None:
    interp.exec(dedent(code))


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
            _exec(
                interp,
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
        assert payload[0] == "ok", payload

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
                _exec(
                    interp,
                    """
                    import sys

                    sys.path.insert(0, package_root)

                    try:
                        import timelog._timelog as c_timelog

                        log = c_timelog.Timelog()
                        try:
                            log.append(1, "alpha")
                            log.flush()
                            row_iter = log.all()
                            span_iter = log.page_spans(0, 10)
                            span = next(span_iter)
                            objects_view = span.objects()
                            objects_iter = iter(objects_view)

                            ids = (
                                id(c_timelog.Timelog),
                                id(c_timelog.TimelogIter),
                                id(c_timelog.PageSpan),
                                id(c_timelog.PageSpanIter),
                                id(c_timelog.PageSpanObjectsView),
                                id(type(objects_iter)),
                            )
                            del objects_iter
                            del objects_view
                            span.close()
                            span_iter.close()
                            row_iter.close()
                        finally:
                            log.close()

                        result_queue.put(
                            (
                                "ok",
                                ids,
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
        assert left_payload[0] == "ok", left_payload
        assert right_payload[0] == "ok", right_payload

        left_ids = left_payload[1]
        right_ids = right_payload[1]

        assert len(left_ids) == len(right_ids) == 6
        assert all(left != right for left, right in zip(left_ids, right_ids, strict=True))
    finally:
        left_interp.close()
        right_interp.close()


def test_subinterpreter_factory_products_use_local_types(
    compat_runtime,
    compat_package_root,
):
    interpreters = compat_runtime.require_subinterpreters()

    result_queue = interpreters.create_queue()
    interp = interpreters.create()
    try:
        interp.prepare_main(
            package_root=compat_package_root,
            result_queue=result_queue,
        )
        try:
            _exec(
                interp,
                """
                import sys

                sys.path.insert(0, package_root)

                try:
                    import timelog._timelog as c_timelog

                    log = c_timelog.Timelog()
                    try:
                        log.append(1, "alpha")
                        log.flush()

                        row_iter = log.all()
                        span_iter = log.page_spans(0, 10)
                        span = next(span_iter)
                        objects_view = span.objects()
                        objects_iter = iter(objects_view)

                        checks = (
                            type(log) is c_timelog.Timelog,
                            type(row_iter) is c_timelog.TimelogIter,
                            type(span_iter) is c_timelog.PageSpanIter,
                            type(span) is c_timelog.PageSpan,
                            type(objects_view) is c_timelog.PageSpanObjectsView,
                            type(objects_iter).__module__ == "timelog._timelog",
                            type(objects_iter).__name__ == "PageSpanObjectsViewIter",
                        )
                        del objects_iter
                        del objects_view
                        span.close()
                        span_iter.close()
                        row_iter.close()
                    finally:
                        log.close()

                    result_queue.put(("ok", checks))
                except Exception as exc:
                    result_queue.put(("error", type(exc).__name__, str(exc)))
                """
            )
        except interpreters.ExecutionFailed as exc:
            raise AssertionError(f"unexpected interpreter execution failure: {exc}") from exc

        payload = result_queue.get(timeout=5.0)
        assert payload[0] == "ok", payload
        assert all(payload[1])
    finally:
        interp.close()


def test_subinterpreter_subclass_method_recovers_module_state(
    compat_runtime,
    compat_package_root,
):
    interpreters = compat_runtime.require_subinterpreters()

    result_queue = interpreters.create_queue()
    interp = interpreters.create()
    try:
        interp.prepare_main(
            package_root=compat_package_root,
            result_queue=result_queue,
        )
        try:
            _exec(
                interp,
                """
                import sys

                sys.path.insert(0, package_root)

                try:
                    import timelog
                    import timelog._timelog as c_timelog

                    class SubTimelog(timelog.Timelog):
                        def fail_from_inherited_c_method(self):
                            self.close()
                            try:
                                self.flush()
                            except c_timelog.TimelogError as exc:
                                return type(exc) is c_timelog.TimelogError
                            return False

                    result_queue.put(("ok", SubTimelog().fail_from_inherited_c_method()))
                except Exception as exc:
                    result_queue.put(("error", type(exc).__name__, str(exc)))
                """
            )
        except interpreters.ExecutionFailed as exc:
            raise AssertionError(f"unexpected interpreter execution failure: {exc}") from exc

        payload = result_queue.get(timeout=5.0)
        assert payload[0] == "ok", payload
        assert payload[1] is True
    finally:
        interp.close()


def test_subinterpreter_close_with_leaked_timelog(
    compat_runtime,
    compat_package_root,
):
    interpreters = compat_runtime.require_subinterpreters()

    result_queue = interpreters.create_queue()
    interp = interpreters.create()
    try:
        interp.prepare_main(
            package_root=compat_package_root,
            result_queue=result_queue,
        )
        try:
            _exec(
                interp,
                """
                import sys

                sys.path.insert(0, package_root)

                try:
                    from timelog import Timelog

                    leaked = Timelog(maintenance="disabled")
                    leaked.append(1, "alpha")
                    result_queue.put(("ok", type(leaked).__name__))
                except Exception as exc:
                    result_queue.put(("error", type(exc).__name__, str(exc)))
                """
            )
        except interpreters.ExecutionFailed as exc:
            raise AssertionError(f"unexpected interpreter execution failure: {exc}") from exc

        payload = result_queue.get(timeout=5.0)
        assert payload[0] == "ok", payload
    finally:
        interp.close()


def test_three_subinterpreters_can_import_and_use_concurrently(
    compat_runtime,
    compat_package_root,
):
    interpreters = compat_runtime.require_subinterpreters()

    interps = [interpreters.create() for _ in range(3)]
    queues = [interpreters.create_queue() for _ in range(3)]
    try:
        for index, (interp, queue) in enumerate(zip(interps, queues, strict=True)):
            interp.prepare_main(
                package_root=compat_package_root,
                result_queue=queue,
                worker_index=index,
            )

        def run(interp):
            try:
                _exec(
                    interp,
                    """
                    import sys

                    sys.path.insert(0, package_root)

                    try:
                        from timelog import Timelog

                        with Timelog(maintenance="disabled") as log:
                            log.append(worker_index, f"value-{worker_index}")
                            rows = tuple(log.all())
                        result_queue.put(("ok", rows))
                    except Exception as exc:
                        result_queue.put(("error", type(exc).__name__, str(exc)))
                    """
                )
            except interpreters.ExecutionFailed as exc:
                raise AssertionError(f"unexpected interpreter execution failure: {exc}") from exc

        with ThreadPoolExecutor(max_workers=3) as executor:
            futures = [executor.submit(run, interp) for interp in interps]
            for future in futures:
                future.result(timeout=10.0)

        payloads = [queue.get(timeout=5.0) for queue in queues]
        assert all(payload[0] == "ok" for payload in payloads), payloads
        assert [tuple(payload[1]) for payload in payloads] == [
            ((0, "value-0"),),
            ((1, "value-1"),),
            ((2, "value-2"),),
        ]
    finally:
        for interp in interps:
            interp.close()


def test_subinterpreter_maintenance_finalize_subprocess(
    compat_runtime,
    compat_package_root,
):
    compat_runtime.require_subinterpreters()

    script = dedent(
        """
        import concurrent.interpreters as interpreters
        import json
        import sys
        from textwrap import dedent

        package_root = sys.argv[1]
        result_queue = interpreters.create_queue()
        interp = interpreters.create()
        try:
            interp.prepare_main(
                package_root=package_root,
                result_queue=result_queue,
            )
            interp.exec(dedent(
                '''
                import sys

                sys.path.insert(0, package_root)

                try:
                    from timelog import Timelog

                    leaked = Timelog(maintenance="background", maintenance_wakeup_ms=1)
                    for i in range(64):
                        leaked.append(i, f"value-{i}")
                    leaked.flush()
                    leaked.stop_maintenance()
                    leaked.start_maintenance()
                    result_queue.put(("ok", len(tuple(leaked.all()))))
                except Exception as exc:
                    result_queue.put(("error", type(exc).__name__, str(exc)))
                '''
            ))
            payload = result_queue.get(timeout=5.0)
            print(json.dumps(payload))
            if payload[0] != "ok":
                raise SystemExit(1)
        finally:
            interp.close()
        """
    )

    env = os.environ.copy()
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        compat_package_root if not existing else compat_package_root + os.pathsep + existing
    )

    completed = subprocess.run(
        [sys.executable, "-c", script, compat_package_root],
        check=False,
        capture_output=True,
        env=env,
        text=True,
        timeout=15.0,
    )

    assert completed.returncode == 0, completed.stderr
    assert json.loads(completed.stdout.strip().splitlines()[-1]) == ["ok", 64]
