"""Debug: Compare C extension vs Python facade for delete+reinsert."""
import sys
sys.path.insert(0, r"U:\Projects\timelog\bindings\cpython\build-test\Debug")
sys.path.insert(0, r"U:\Projects\timelog\python")

# Test 1: Direct C extension (no Python facade)
print("=" * 60)
print("TEST 1: Direct C extension (_CTimelog)")
print("=" * 60)

from timelog._timelog import Timelog as _CTimelog

log = _CTimelog(maintenance="disabled")
log.append(100, "a")
print(f"  After append(100,'a'): point(100) = {list(log.point(100))}")

log.delete_range(100, 101)
print(f"  After delete_range(100,101): point(100) = {list(log.point(100))}")

log.append(100, "b")
result = list(log.point(100))
print(f"  After append(100,'b'): point(100) = {result}")

# Also try range query
result_range = list(log.range(99, 102))
print(f"  range(99,102) = {result_range}")

# Full scan
result_all = list(log.since(-9223372036854775808))
print(f"  since(MIN) = {result_all}")

# Validate
try:
    log.validate()
    print(f"  validate() = OK")
except Exception as e:
    print(f"  validate() = FAILED: {e}")

log.close()

# Test 2: Python facade (Timelog)
print()
print("=" * 60)
print("TEST 2: Python facade (Timelog)")
print("=" * 60)

from timelog import Timelog

log2 = Timelog(maintenance="disabled")
log2.append(100, "a")
print(f"  After append(100,'a'): log[100] = {log2[100]}")

log2.delete(100)
print(f"  After delete(100): log[100] = {log2[100]}")

log2.append(100, "b")
result2 = log2[100]
print(f"  After append(100,'b'): log[100] = {result2}")

# Also try range
result2_range = list(log2[99:102])
print(f"  log[99:102] = {result2_range}")

# Full scan
result2_all = list(log2)
print(f"  list(log) = {result2_all}")

log2.close()

# Test 3: C extension with integer handles (like C test)
print()
print("=" * 60)
print("TEST 3: C extension with simple integer handles")
print("=" * 60)

log3 = _CTimelog(maintenance="disabled")
log3.append(100, 1)
print(f"  After append(100, 1): point(100) = {list(log3.point(100))}")

log3.delete_range(100, 101)
print(f"  After delete_range(100,101): point(100) = {list(log3.point(100))}")

log3.append(100, 2)
result3 = list(log3.point(100))
print(f"  After append(100, 2): point(100) = {result3}")

result3_range = list(log3.range(99, 102))
print(f"  range(99,102) = {result3_range}")

result3_all = list(log3.since(-9223372036854775808))
print(f"  since(MIN) = {result3_all}")

log3.close()

# Test 4: C extension with wider delete range (like C test uses 100-200)
print()
print("=" * 60)
print("TEST 4: C extension with wider delete range [100,200)")
print("=" * 60)

log4 = _CTimelog(maintenance="disabled")
log4.append(100, 1)
log4.delete_range(100, 200)  # Wider range like the C test
log4.append(100, 2)
result4 = list(log4.point(100))
print(f"  point(100) = {result4}")
result4_range = list(log4.range(99, 102))
print(f"  range(99,102) = {result4_range}")
log4.close()

# Test 5: Check sequence of operations with stats
print()
print("=" * 60)
print("TEST 5: Stats check")
print("=" * 60)

log5 = _CTimelog(maintenance="disabled")
log5.append(100, "a")
s = log5.stats()
print(f"  After insert: records_estimate={s.get('records_estimate', '?')}")

log5.delete_range(100, 101)
s = log5.stats()
print(f"  After delete: records_estimate={s.get('records_estimate', '?')}")

log5.append(100, "b")
s = log5.stats()
print(f"  After reinsert: records_estimate={s.get('records_estimate', '?')}")

# Point query
pt = list(log5.point(100))
print(f"  point(100) = {pt}")

# Check: does flush help?
log5.flush()
pt_after_flush = list(log5.point(100))
print(f"  After flush, point(100) = {pt_after_flush}")

log5.close()
