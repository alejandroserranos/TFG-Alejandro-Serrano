method ordenar_quicksort(V : array?<int>)
    requires V != null
    modifies V
    ensures segmento_ordenado(V, 0, V.Length)
    ensures multiset(V[..]) == multiset(old(V[..]))
{
    quicksort(V, 0, V.Length);
}

predicate segmento_ordenado(V : array?<int>, c : int, f : int)
    requires V != null && 0 <= c <= f <= V.Length
    reads V
{
    forall j, k :: c <= j < k < f ==> V[j] <= V[k]
}

method quicksort(V : array?<int>, c : int, f : int)
    requires V != null && 0 <= c <= f <= V.Length
    modifies V
    ensures segmento_ordenado(V, c, f)
    ensures multiset(V[c..f]) == multiset(old(V[c..f]))
{
    if f - c > 1 {
        var pivote: int;
        pivote := particion(V, c, f);
        quicksort(V, c, pivote);
        quicksort(V, pivote + 1, f);
    }
}

method particion(V : array?<int>, c : int, f : int) returns (pivote : int)
    requires V != null && 0 <= c < f <= V.Length
    modifies V
    ensures c <= pivote < f
    ensures multiset(V[c..f]) == multiset(old(V[c..f]))
    ensures forall i :: c <= i < pivote ==> V[i] < V[pivote]
    ensures forall i :: pivote < i < f ==> V[i] >= V[pivote]
{
    pivote := c;
    var indice: nat := c + 1;
    while indice < f
        invariant c + 1 <= indice <= f
        invariant c <= pivote < indice
        invariant multiset(V[c..indice]) == multiset(old(V[c..indice]))
        decreases f - indice
    {
        if V[indice] < V[pivote] {
            var contador: nat := indice - 1;
            var temp: int := V[indice];
            V[indice] := V[contador];

            while contador > pivote
                invariant pivote < contador <= indice - 1
                invariant V[pivote + 1..contador + 1] == old(V[pivote..contador])
                decreases contador - pivote
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
