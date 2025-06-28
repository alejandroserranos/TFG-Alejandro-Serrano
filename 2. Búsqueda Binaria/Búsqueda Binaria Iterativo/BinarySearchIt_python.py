from typing import List, Tuple

def ordenado(s: List[int]) -> bool:
    return all(s[i] <= s[j] for i in range(len(s)) for j in range(i, len(s)))

def binary_search_it(V: List[int], x: int, c: int, f: int) -> Tuple[bool, int]:
    assert V is not None
    assert 0 <= c <= f <= len(V)
    assert ordenado(V[c:f])

    c_, f_ = c, f
    m = (c_ + f_) // 2

    while c_ < f_ and V[m] != x:
        if x < V[m]:
            f_ = m
        else:
            c_ = m + 1
        m = (c_ + f_) // 2

    if c_ == f_:
        return False, c_
    else:
        return True, m
