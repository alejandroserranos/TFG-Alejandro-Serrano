/*
Actúa como un asistente experto en Dafny que transforma el código dado sin especificaciones 
en una versión funcionalmente idéntica pero con las especificaciones formales necesarias y suficientes 
para que Dafny lo verifique automáticamente.

Contexto (úsalo tal cual):

predicate isSorted(a : array?<int>)
  requires a != null
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

Reglas estrictas:

- Salida: exclusivamente el código Dafny final, sin comentarios ni explicaciones.
- Intocables: no cambies la lógica, el orden de sentencias, los nombres de métodos/variables 
  ni el formato (sangrado, espacios y saltos de línea), salvo para insertar cláusulas de especificación.
- Orden de inserción (solo si son necesarias):
  1. requires
  2. ensures
  3. modifies
  4. decreases

- Bucles: añade invariantes (invariant) adecuados y, si es necesario, una cota de terminación (decreases) 
  para garantizar la terminación.
- Nada nuevo: no declares métodos, predicados ni funciones adicionales; prioriza siempre precondiciones, 
  postcondiciones e invariantes locales.
- Lecturas/escrituras: usa reads/modifies apropiados para los efectos del programa.

Devuélveme únicamente el código transformado, sin comentarios.

Código sin especificaciones a transformar:
*/

predicate isSorted(a : array?<int>)

    requires a != null
    reads a

{

    forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]

}


method SelectionSort(a: array<int>) 

    requires a != null
    modifies a
    ensures isSorted(a)

{

  var n := 0;

  while (n != a.Length)

    invariant 0 <= n <= a.Length
    invariant forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant forall i,k :: 0 <= i < n && n <= k < a.Length ==> a[i] <= a[k]

    decreases a.Length - n

  {

    var mindex := n;
    var m := n + 1;

    while (m != a.Length)

      invariant n < m <= a.Length
      invariant n <= mindex < m
      invariant forall t :: n <= t < m ==> a[mindex] <= a[t]

      decreases a.Length - m

    {

      if (a[m] < a[mindex]) {

        mindex := m;

      }

      m := m + 1;

    }

    a[n], a[mindex] := a[mindex], a[n] ;
    n := n + 1;

  }

}
