predicate es_pico(s : seq<int>)

    requires |s| > 0

{

    forall j : nat | j < |s| - 1 :: s[|s| - 1] >= s[j]

}

function sumapicos(s : seq <int>) : int 

{

    if s == [] then 0 
        else sumapicos(s[..|s| - 1]) + ( if es_pico(s) then s[|s| - 1] else 0 )

}

method suma_picos(V : array?<int>) returns (s : int)

    requires V != null && V.Length > 0
    ensures  s == sumapicos(V[..])

{

    var n : nat, m : int ;
    n, s, m := 1, V[0], V[0] ;

    while n != V.Length

        invariant 0 <= n <= V.Length
        invariant s == sumapicos(V[..n]) 
        invariant forall j | 0 <= j < n :: m >= V[j]
        invariant exists j | 0 <= j < n :: m == V[j]

        decreases V.Length - n

    {

        assert V[..n + 1][..n] == V[..n] ;

        if V[n] >= m {

            assert es_pico(V[..n + 1]) ;

            s := s + V[n] ;

        }

        m := if m > V[n] then m else V[n] ;
        n := n + 1 ;

    }

    assert V[..n] == V[..] ;
    
}