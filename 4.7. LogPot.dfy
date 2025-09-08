function pot (a : int, b : int) : int

{

    if b == 0 then 1
    else a * pot(a, b - 1)

}

method log_ent (n : nat, b : nat) returns (r : nat)

{
    
    var p : int ;

    r := 0 ;
    p := b ;

    while p <= n 

    {

        p := p * b ;
        r := r + 1 ;

    }

}