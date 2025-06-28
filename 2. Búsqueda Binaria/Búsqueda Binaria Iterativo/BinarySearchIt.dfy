predicate ordenado(s : seq<int>)      
{
	forall i, j | 0 <= i <= j <= |s| - 1 :: s[i] <= s[j]
}

method busqueda_binaria_it(V : array?<int>, x : int, c : nat, f : nat) returns (b : bool, p : nat)
{
	var m : nat ;
	m := (c + f) / 2 ;
	var c', f' : nat ;
	c', f' := c, f;
	while c' < f' && x != V[m]
	{
		if x < V[m] {
			f' := m ;
		} else {
			c' := m + 1 ;
		}
		m := (c' + f') / 2 ;
	}
	if c' == f' {
		b, p := false, c' ;
	} else {
		b, p := true, m ;
	}
}
