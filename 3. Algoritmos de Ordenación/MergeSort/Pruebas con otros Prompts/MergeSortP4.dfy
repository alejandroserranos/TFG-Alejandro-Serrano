method ordenar_mergesort(V: array?<int>)
    requires V != null
    modifies V
    ensures multiset(V[..]) == multiset(old(V[..]))
    ensures forall i: int :: 0 <= i < V.Length - 1 ==> V[i] <= V[i + 1]
{
    mergesort(V, 0, V.Length - 1);
}

method mergesort(V: array?<int>, c: int, f: int)
    requires V != null && 0 <= c <= f + 1 <= V.Length
    modifies V
    ensures multiset(V[..]) == multiset(old(V[..]))
    ensures forall i: int :: 0 <= i < V.Length - 1 ==> V[i] <= V[i + 1]
{
    if c < f {
        var m: int;
        m := c + (f - c) / 2;
        mergesort(V, c, m);
        mergesort(V, m + 1, f);
        mezclar(V, c, m, f);
    }
}

method mezclar(V: array?<int>, c: int, m: int, f: int)
    requires V != null && 0 <= c <= m < f < V.Length
    modifies V
    ensures multiset(V[c..f+1]) == multiset(old(V[c..f+1]))
    ensures forall i: int :: c <= i < f ==> V[i] <= V[i + 1]
{
    var V1: array?<int>;
    var j: nat;
    if m - c + 1 > 0 {
        V1 := new int[m - c + 1](i => 0);
        j := 0;
        while j < V1.Length && c + j < V.Length
            invariant 0 <= j <= V1.Length
            invariant c + j <= V.Length
            invariant forall k: int :: 0 <= k < j ==> V1[k] == V[c + k]
            decreases V1.Length - j
        {
            V1[j] := V[c + j];
            j := j + 1;
        }
    } else {
        V1 := new int[0];
    }

    var V2: array?<int>;
    var k: nat;
    V2 := new int[f - m](i => 0);
    k := 0;
    while k < V2.Length && m + k + 1 < V.Length
        invariant 0 <= k <= V2.Length
        invariant m + k + 1 <= V.Length
        invariant forall l: int :: 0 <= l < k ==> V2[l] == V[m + 1 + l]
        decreases V2.Length - k
    {
        V2[k] := V[m + k + 1];
        k := k + 1;
    }

    var i: nat;
    i := 0;
    j := 0;
    k := 0;
    while i < f - c + 1 &&
          j <= V1.Length &&
          k <= V2.Length &&
          c + i < V.Length
        invariant 0 <= i <= f - c + 1
        invariant 0 <= j <= V1.Length
        invariant 0 <= k <= V2.Length
        invariant c + i <= V.Length
        invariant multiset(V[c .. c + i]) ==
                   multiset(V1[..j]) + multiset(V2[..k])
        invariant forall t: int :: c <= t < c + i - 1 ==> V[t] <= V[t + 1]
        decreases f - c + 1 - i
    {
        if j >= V1.Length && k >= V2.Length {
            break;
        } else if j >= V1.Length {
            V[c + i] := V2[k];
            k := k + 1;
        } else if k >= V2.Length {
            V[c + i] := V1[j];
            j := j + 1;
        } else {
            if V1[j] <= V2[k] {
                V[c + i] := V1[j];
                j := j + 1;
            } else {
                V[c + i] := V2[k];
                k := k + 1;
            }
        }
        i := i + 1;
    }
}
