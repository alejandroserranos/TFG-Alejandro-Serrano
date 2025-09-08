/*
Eres un experto en verificación formal en el lenguaje Dafny. Voy a proporcionarte un método escrito en Dafny que no contiene especificaciones. 
Tu tarea consiste en aportar:

1. Una precondición adecuada (requires).
2. Una postcondición (ensures).

El código es:

*/

method SimpleVerification(x: int) returns (y: int)

    ensures y == x + 1

{

    y := x + 1;

}