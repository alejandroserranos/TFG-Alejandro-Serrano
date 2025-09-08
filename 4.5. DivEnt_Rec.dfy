method DivEntR(a : int, b : int) returns (q : int, r : int)  

{

    var q1, r1 : int ;

    if a < b {

        q, r := 0, a ;

    } else {

        q1, r1 := DivEntR(a - b, b) ;
        q, r   := q1 + 1, r1 ; 

    }
    
}