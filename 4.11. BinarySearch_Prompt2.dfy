/*
Estoy trabajando en mi Trabajo de Fin de Grado sobre verificación formal usando Dafny. 
A continuación se muestra un programa en Dafny que es funcionalmente correcto, 
pero que no incluye ninguna especificación formal (como precondiciones, 
postcondiciones, invariantes de bucle o declaraciones auxiliares).

Por favor, añade todas las especificaciones necesarias para que el programa pueda ser 
verificado formalmente en Dafny, teniendo en cuenta el siguiente entorno de trabajo:

- Sistema operativo: Windows 11 Home, versión 24H2 (compilación 26100.4061)
- Procesador: 11th Gen Intel(R) Core(TM) i5-1135G7 @ 2.40GHz
- RAM: 8.00 GB
- Editor de código: Visual Studio Code, versión 1.100.3, con la extensión oficial de Dafny habilitada
- Lenguaje de verificación: Dafny, versión 3.4.4
- Verificador SMT subyacente: Z3 (versión incluida con Dafny)
- Asistente LLM: ChatGPT (GPT-4-turbo), accedido mediante la interfaz de OpenAI

Indicaciones:

- Incluir:
  * requires (precondiciones)
  * ensures (postcondiciones)
  * invariant (invariantes de bucle, si corresponde)

Aquí está el código Dafny sin especificaciones:
*/

method BinarySearch(a: array?<int>, x: int) returns (index: int)

    requires a != null
    requires a.Length >= 0
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]  // array is sorted non-decreasingly
    ensures (index == -1) <==> (forall k :: 0 <= k < a.Length ==> a[k] != x)
    ensures 0 <= index < a.Length ==> a[index] == x

{

    var low := 0;
    var high := a.Length - 1;

    while low <= high

        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant forall i :: 0 <= i < low ==> a[i] < x
        invariant forall i :: high < i < a.Length ==> a[i] > x

    {

        var mid := low + (high - low) / 2;

        if a[mid] == x {

            return mid;

        } else if a[mid] < x {

            low := mid + 1;

        } else { 

            high := mid - 1;

        }

    }

    return -1;
    
}
