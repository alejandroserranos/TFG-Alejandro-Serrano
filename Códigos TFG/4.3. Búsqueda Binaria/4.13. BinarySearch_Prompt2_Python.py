from typing import List

def binary_search(a: List[int], x: int) -> int:
    assert a is not None
    assert all(a[i] <= a[i+1] for i in range(len(a)-1))
    low, high = 0, len(a) - 1
    while low <= high:
        assert 0 <= low <= len(a)
        assert -1 <= high < len(a) or len(a) == 0
        assert all(a[i] < x for i in range(low))
        assert all(a[i] > x for i in range(high+1, len(a)))
        mid = low + (high - low) // 2
        if a[mid] == x:
            assert 0 <= mid < len(a) and a[mid] == x
            return mid
        elif a[mid] < x:
            low = mid + 1
        else:
            high = mid - 1
    assert all(val != x for val in a)
    return -1