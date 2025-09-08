method DivisionEntera(a: nat, b: nat) returns (cociente: nat, resto: nat)

{

    var q := 0;
    var r := a;

    while r >= b

    {

        r := r - b;
        q := q + 1;

    }

    cociente := q;
    resto := r;
    
}