predicate sorted(a: seq<int>) {
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate permutation(a: seq<int>, b: seq<int>) {
    multiset(a) == multiset(b)
}

method ordenar_mergesort(V: array<int>)
    requires V != null
    modifies V
    ensures sorted(V[..])
    ensures permutation(V[..], old(V[..]))
{
    mergesort(V, 0, V.Length - 1);
}

method mergesort(V: array<int>, c: int, f: int)
    requires V != null
    requires 0 <= c <= f + 1 <= V.Length
    modifies V
    ensures sorted(V[c..f+1])
    ensures permutation(V[c..f+1], old(V[c..f+1]))
{
    if c < f {
        var m := c + (f - c) / 2;
        mergesort(V, c, m);
        mergesort(V, m + 1, f);
        mezclar(V, c, m, f);
    }
}

method mezclar(V: array<int>, c: int, m: int, f: int)
    requires V != null
    requires 0 <= c <= m < f < V.Length
    requires sorted(V[c..m+1]) && sorted(V[m+1..f+1])
    modifies V
    ensures sorted(V[c..f+1])
    ensures permutation(V[c..f+1], old(V[c..f+1]))
{
    var V1 := new int[m - c + 1](i => V[c + i]);
    var V2 := new int[f - m](i => V[m + 1 + i]);

    var i := 0;
    var j := 0;
    var k := 0;

    while i < f - c + 1 && c + i < V.Length
        invariant 0 <= i <= f - c + 1
        invariant 0 <= j <= V1.Length
        invariant 0 <= k <= V2.Length
        invariant c + i <= V.Length
        invariant permutation(V[c..c+i], V1[..j] + V2[..k])
        invariant sorted(V[c..c+i])
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
