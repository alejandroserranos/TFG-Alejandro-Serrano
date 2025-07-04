method ordenar_mergesort(V : array?<int>)
    requires V != null
    modifies V
{
    mergesort(V, 0, V.Length - 1);
}

method mergesort(V : array?<int>, c : int, f : int) 
    requires V != null && 0 <= c <= f + 1 <= V.Length
    modifies V
    decreases f - c + 1
{
    if c < f {
        var m := c + (f - c) / 2;
        mergesort(V, c, m);
        mergesort(V, m + 1, f);
        mezclar(V, c, m, f);
    }
}

method mezclar(V: array?<int>, c : int, m : int, f : int)
    requires V != null && 0 <= c <= m < f < V.Length
    modifies V
{
    var V1 := new int[m - c + 1](i => 0);
    var j : nat := 0;
    while j < V1.Length
        invariant 0 <= j <= V1.Length
        invariant forall k :: 0 <= k < j ==> V1[k] == V[c + k]
        decreases V1.Length - j
    {
        V1[j] := V[c + j];
        j := j + 1;
    }

    var V2 := new int[f - m](i => 0);
    var k : nat := 0;
    while k < V2.Length
        invariant 0 <= k <= V2.Length
        invariant forall l :: 0 <= l < k ==> V2[l] == V[m + 1 + l]
        decreases V2.Length - k
    {
        V2[k] := V[m + 1 + k];
        k := k + 1;
    }

    var i : nat := 0;
    j := 0;
    k := 0;

    while i < f - c + 1 && (j < V1.Length || k < V2.Length)
        invariant 0 <= i <= f - c + 1
        invariant 0 <= j <= V1.Length
        invariant 0 <= k <= V2.Length
        decreases f - c + 1 - i
    {
        if j >= V1.Length && k >= V2.Length {
            break;
        }
        else if j >= V1.Length {
            V[c + i] := V2[k];
            k := k + 1;
        }
        else if k >= V2.Length {
            V[c + i] := V1[j];
            j := j + 1;
        }
        else {
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



