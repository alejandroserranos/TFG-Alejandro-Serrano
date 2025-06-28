function method sorted(s: seq<int>): bool {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function method multiset_eq(s1: seq<int>, s2: seq<int>): bool {
  multiset(s1) == multiset(s2)
}

method ordenar_mergesort(V : array?<int>)
    requires V != null
    requires V.Length >= 0
    modifies V
    ensures sorted(V[..])
    ensures multiset_eq(V[..], old(V[..]))
{
    mergesort(V, 0, V.Length - 1);
}

method mergesort(V : array?<int>, c : int, f : int) 
    requires V != null
    requires 0 <= c <= f + 1 <= V.Length
    modifies V
    ensures sorted(V[c..f+1])
    ensures multiset_eq(V[c..f+1], old(V[c..f+1]))
{
    if c < f {
        var m : int;
        m := c + (f - c) / 2;
        mergesort(V, c, m);
        mergesort(V, m + 1, f);
        mezclar(V, c, m, f);
    } 
}

method mezclar(V: array?<int>, c : int, m : int, f : int)
    requires V != null
    requires 0 <= c <= m < f < V.Length
    requires sorted(V[c..m+1]) && sorted(V[m+1..f+1])
    requires multiset_eq(V[c..m+1] + V[m+1..f+1], V[c..f+1])
    modifies V
    ensures sorted(V[c..f+1])
    ensures multiset_eq(V[c..f+1], old(V[c..f+1]))
{
    var V1 : array?<int>;
    var j  : nat;
    if m - c + 1 > 0 {
        V1 := new int[m - c + 1](i => 0);
        j  := 0;
        while j < V1.Length && c + j < V.Length
        {
            V1[j] := V[c + j];
            j := j + 1;
        }
    } else {
        V1 := new int[0];
    }

    var V2 : array?<int>;
    var k  : nat;
    V2 := new int[f - m](i => 0);
    k  := 0;
    while k < V2.Length && m + k + 1 < V.Length
    {
        V2[k] := V[m + k + 1];
        k := k + 1;
    }

    var i : nat;
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
        invariant multiset_eq(V[c .. c + i], V1[..j] + V2[..k])
        invariant sorted(V[c .. c + i])
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
            } else if V1[j] > V2[k] {
                V[c + i] := V2[k];
                k := k + 1;
            }
        }
        i := i + 1;  
    }  
}
