/*
A continuación te doy un código en Dafny funcionalmente correcto pero sin ninguna 
especificación formal. Por favor, añádele todas las especificaciones necesarias para que 
sea verificable automáticamente en Dafny: precondiciones (requires), postcondiciones (ensures), 
invariantes de bucle (invariant), y funciones de cota (decreases) que garanticen la terminación.

Asegúrate de que:

- Todo acceso a arrays esté correctamente acotado por precondiciones.
- Cada bucle tenga invariantes adecuados y una función de cota decreciente.
- El código final sea correcto según los criterios de verificación formal de Dafny.

Aquí tienes el código sin especificaciones:
*/

method BinarySearch(a: array?<int>, x: int) returns (index: int)

    requires a != null
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]  // el array está ordenado
    ensures (index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != x) // si no se encontró, no está
    ensures (0 <= index < a.Length ==> a[index] == x)              // si se encontró, es correcto

{

    var low := 0;
    var high := a.Length - 1;

    while low <= high

        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant low <= high + 1 // garantiza que el rango es válido
        invariant forall i :: 0 <= i < low ==> a[i] < x // todo lo que ya descartamos < x
        invariant forall i :: high < i < a.Length ==> a[i] > x // todo lo que descartamos > x

        decreases high - low + 1

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