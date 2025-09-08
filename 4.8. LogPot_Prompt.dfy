/*
Quiero que actúes como un asistente experto en Dafny que transforma cualquier código funcionalmente idéntico añadiendo solo especificaciones formales suficientes para que Dafny pueda verificarlo automáticamente.
Sigue estas reglas estrictas:
1.	Salida: exclusivamente el código Dafny final, sin comentarios ni explicaciones adicionales.
2.	Intocables: no cambies la lógica, el orden de sentencias, nombres de métodos/variables ni el formato original salvo para insertar cláusulas de especificación.
3.	Dónde y cómo insertar (y en este orden):
    o	requires (todas las precondiciones necesarias),
    o	ensures (las postcondiciones requeridas para la verificación),
    o	modifies (si es necesario),
    o	decreases (si es necesario para terminación).
4.	En cada bucle debes añadir invariantes (invariant) adecuados y, si es imprescindible, una función de cota (decreases) para garantizar la terminación.
5.	No declares métodos o predicados nuevos; prioriza siempre precondiciones, postcondiciones e invariantes locales.
6.	Mantén el estilo y espacios del código original. Donde insertes especificaciones, respeta las sangrías y coloca líneas en blanco como si formaran parte natural del código.
7.	Si el programa ya es verificable sin decreases, no lo añadas.
Tarea: cuando te dé un código sin especificaciones, debes devolverme exclusivamente ese mismo código en Dafny con las especificaciones formales insertadas, siguiendo estas reglas.
El código sin especificaciones es:
*/

function pot (a : int, b : int) : int

    requires b >= 0

    decreases b

{

    if b == 0 then 1
    else a * pot(a, b - 1)

}

method log_ent (n : nat, b : nat) returns (r : nat)

    requires n > 0 && b > 1
    ensures  pot(b, r) <= n && n < pot(b, r + 1)

{

    var p : int ;
    r := 0 ;
    p := b ;

    while p <= n 

        invariant r >= 0
        invariant pot(b, r) <= n
        invariant p == pot(b, r + 1)

        decreases n - pot(b, r)
        
    {

        p := p * b ;
        r := r + 1 ;

    }
    
}
