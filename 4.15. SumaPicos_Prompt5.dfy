/*
Actúa como un asistente experto en Dafny que transforma el código dado sin especificaciones en una versión funcionalmente idéntica, pero con las especificaciones formales necesarias y suficientes para que Dafny pueda verificarlo automáticamente.
Reglas:
    •	Salida: exclusivamente el código Dafny final, sin comentarios ni explicaciones adicionales.
    •	Intocables: no cambies la lógica, el orden de sentencias, nombres de métodos/variables ni el formato original (sangrado, espacios, saltos de línea), salvo para insertar cláusulas de especificación.
    •	Inserción y orden (solo si son necesarias):
        1.	requires
        2.	ensures
        3.	modifies
        4.	decreases
    •	Bucles: añade invariantes (invariant) adecuados y, si es necesario, una cota de terminación (decreases) para garantizar la terminación.
    •	Nada nuevo: no declares métodos, predicados ni funciones adicionales; prioriza siempre precondiciones, postcondiciones e invariantes locales.
Contexto (debe tenerse en cuenta para crear las especificaciones):
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
Tarea:
    Devuélveme únicamente el código Dafny final, con las especificaciones necesarias insertadas para que Dafny lo verifique correctamente, manteniendo exactamente el formato y la lógica del código original.
Código sin especificaciones:
*/

predicate es_pico(s : seq<int>)

    requires |s| > 0

{

    forall j : nat | j < |s| - 1 :: s[|s| - 1] >= s[j]

}

function sumapicos(s : seq <int>) : int 

    decreases |s|

{

    if s == [] then 0 
        else sumapicos(s[..|s| - 1]) + ( if es_pico(s) then s[|s| - 1] else 0 )

}

method suma_picos(V : array?<int>) returns (s : int)

    requires V != null && V.Length > 0
    ensures s == sumapicos(V[..])

{

    var n : nat, m : int ;
    n, s, m := 1, V[0], V[0] ;

    while n != V.Length

        invariant 1 <= n <= V.Length
        invariant s == sumapicos(V[..n])
        invariant forall j : nat | j < n :: m >= V[j]
        invariant exists i : nat :: i < n && m == V[i]

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
