predicate segmento_ordenado(V: array?<int>, c: int, f: int)
    reads V
{
    forall j, k :: c <= j < k < f ==> V[j] <= V[k]
}

predicate permutacion(V1: array?<int>, V2: array?<int>, c: int, f: int)
    reads V1, V2
{
    multiset(V1[c..f]) == multiset(V2[c..f])
}

// Método principal: especificación general
method ordenar_quicksort(V: array?<int>)
    requires V != null
    modifies V
    ensures segmento_ordenado(V, 0, V.Length)
    ensures multiset(V[..]) == old(multiset(V[..]))
{
    quicksort(V, 0, V.Length);
}

// Quicksort sobre segmento [c, f)
method quicksort(V: array?<int>, c: int, f: int)
    requires V != null && 0 <= c <= f <= V.Length
    modifies V
    ensures segmento_ordenado(V, c, f)
    ensures multiset(V[c..f]) == old(multiset(V[c..f]))
{
    if f - c > 1 {
        var pivote: int;
        pivote := particion(V, c, f);
        quicksort(V, c, pivote);
        quicksort(V, pivote + 1, f);
    }
}

// Partición del segmento [c, f), devuelve posición final del pivote
method particion(V: array?<int>, c: int, f: int) returns (pivote: int)
    requires V != null && 0 <= c < f <= V.Length
    modifies V
    ensures c <= pivote < f
    ensures forall i :: c <= i < pivote ==> V[i] < V[pivote]
    ensures forall i :: pivote < i < f ==> V[i] >= V[pivote]
    ensures multiset(V[c..f]) == old(multiset(V[c..f]))
{
    pivote := c;
    var indice: nat := c + 1;

    while indice < f
        invariant c <= pivote < f
        invariant c + 1 <= indice <= f
        invariant forall i :: c <= i < pivote ==> V[i] < V[pivote]
        invariant forall i :: pivote < i < indice ==> V[i] >= V[pivote]
        invariant multiset(V[c..indice]) == old(multiset(V[c..indice]))
    {
        if V[indice] < V[pivote] {
            var contador: nat := indice - 1;
            var temp: int := V[indice];
            V[indice] := V[contador];

            while contador > pivote
                invariant pivote <= contador <= indice - 1
                invariant multiset(V[c..indice]) == old(multiset(V[c..indice]))
            {
                V[contador + 1] := V[contador];
                contador := contador - 1;
            }

            V[pivote + 1] := V[pivote];
            pivote := pivote + 1;
            V[pivote - 1] := temp;
        }
        indice := indice + 1;
    }
}
