predicate ordenado(s: seq<int>)
{
  forall i, j | 0 <= i <= j < |s| :: s[i] <= s[j]
}

method BinarySearch_it(V: array?<int>, x: int, c: nat, f: nat) returns (b: bool, p: nat)
  requires V != null
  requires 0 <= c <= f <= V.Length
  requires ordenado(V[c..f])
  ensures (b ==> (c <= p < f && V[p] == x)) &&
          (!b ==> (forall i :: c <= i < f ==> V[i] != x))
{
  var m: nat;
  m := (c + f) / 2;
  var c', f': nat;
  c', f' := c, f;

  while c' < f' && x != V[m]
    invariant c <= c' <= f' <= f
    invariant forall i :: c <= i < c' ==> V[i] < x
    invariant forall i :: f' <= i < f ==> V[i] > x
    invariant m == (c' + f') / 2
    decreases f' - c'
  {
    if x < V[m] {
      f' := m;
    } else {
      c' := m + 1;
    }
    m := (c' + f') / 2;
  }

  if c' == f' {
    b, p := false, c';
  } else {
    b, p := true, m;
  }
}