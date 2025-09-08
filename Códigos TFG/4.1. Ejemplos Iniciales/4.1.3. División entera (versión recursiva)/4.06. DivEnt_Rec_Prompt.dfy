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
6.	Si el programa ya es verificable sin decreases, no lo añadas.
Tarea: cuando te dé un código sin especificaciones, debes devolverme exclusivamente ese mismo código en Dafny con las especificaciones formales insertadas, siguiendo estas reglas.
El código sin especificaciones es:
*/

method DivEntR(a : int, b : int) returns (q : int, r : int) 

    requires a >= 0
    requires b > 0
    ensures a == q * b + r
    ensures 0 <= r < b

    decreases a

{

    var q1, r1 : int ;

    if a < b {

        q, r := 0, a ;

    } else {

        q1, r1 := DivEntR(a - b, b) ;
        q, r   := q1 + 1, r1 ; 

    }
    
}
