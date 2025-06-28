predicate ordenado(s: seq<int>)
{
  forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

method busqueda_binaria_it(V: array<int>, x: int, c: nat, f: nat) returns (b: bool, p: nat)
  requires V != null
  requires 0 <= c <= f <= V.Length
  requires ordenado(V[c..f])
  ensures b ==> (c <= p < f && V[p] == x)
  ensures !b ==> (p == f || (c <= p < f && V[p] != x))
  ensures forall i :: c <= i < f ==> (b ==> (V[i] == x ==> i == p))
{
  var c', f' := c, f;
  var m := (c' + f') / 2;

  while c' < f' && V[m] != x
    invariant c <= c' <= f' <= f
    invariant f' <= V.Length
    invariant ordenado(V[c'..f'])
    invariant (forall i :: c <= i < f ==> (x == V[i]) ==> (c' <= i < f'))
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
