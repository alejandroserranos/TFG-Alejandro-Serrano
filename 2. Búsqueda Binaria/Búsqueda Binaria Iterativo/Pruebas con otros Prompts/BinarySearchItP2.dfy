predicate ordenado(s: seq<int>)
{
  forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

method busqueda_binaria_it(V: array?<int>, x: int, c: nat, f: nat) returns (b: bool, p: nat)
  requires V != null
  requires ordenado(V[..])
  requires c <= f <= V.Length
  ensures b ==> (c <= p < f && V[p] == x)
  ensures !b ==> (forall i :: c <= i < f ==> V[i] != x)
{
  var c', f' := c, f;
  var m: nat := (c' + f') / 2;

  while c' < f' && x != V[m]
    invariant c <= c' <= f' <= f <= V.Length
    invariant forall i :: c <= i < c' ==> V[i] < x
    invariant forall i :: f' <= i < f ==> V[i] > x
    invariant c' <= m < f'
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
