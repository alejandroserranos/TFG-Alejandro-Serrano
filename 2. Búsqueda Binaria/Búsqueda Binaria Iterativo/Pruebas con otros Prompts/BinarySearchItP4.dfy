predicate ordenado(s: seq<int>)      
{
  forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

method busqueda_binaria_it(V: array?<int>, x: int, c: nat, f: nat) returns (b: bool, p: nat)
  requires V != null
  requires c <= f <= V.Length
  ensures (b ==> (p < f && V[p] == x))
  ensures (!b ==> (p == f || (p < f && V[p] != x)))
  ensures forall i :: c <= i < f && i != p ==> V[i] != x
  modifies {}
{
  var m: nat;
  m := (c + f) / 2;

  var c', f': nat;
  c', f' := c, f;

  while c' < f' && x != V[m]
    invariant c <= c' <= f' <= f
    invariant c' <= m < f'
    invariant forall i :: c <= i < c' ==> V[i] < x
    invariant forall i :: f' <= i < f ==> V[i] > x
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