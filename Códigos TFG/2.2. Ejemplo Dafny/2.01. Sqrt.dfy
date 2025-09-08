method Sqrt(n: nat) returns (r: nat)

    requires n >=0
    ensures r * r <= n < (r + 1) * (r + 1)

{

    var x :=0;

    while (x + 1) * (x + 1) <= n

        invariant 0 <= x <= n
        invariant x * x <= n

    {

        x := x + 1;

    }

    r := x;
    
}