/*
Eres un experto en verificación formal en el lenguaje Dafny. Voy a proporcionarte un método escrito en Dafny que no contiene especificaciones. 
Tu tarea consiste en aportar:

1. Una precondición adecuada (requires).
2. Una postcondición (ensures).
3. Invariantes de bucle (invariant).

El código es:
*/

method BinarySearch(a: array<int>, x: int) returns (index: int)

    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures (index != -1 ==> 0 <= index < a.Length && a[index] == x)
          && (index == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != x)

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
