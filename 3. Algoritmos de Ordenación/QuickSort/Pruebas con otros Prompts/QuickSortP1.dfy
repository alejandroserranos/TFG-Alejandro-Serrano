predicate segmento_ordenado(V : array?<int>, c : int, f : int)
    reads V
{
    forall j, k :: c <= j < k < f ==> V[j] <= V[k]
}

method ordenar_quicksort(V : array?<int>)
    requires V != null
    modifies V
    ensures segmento_ordenado(V, 0, V.Length)
    ensures multiset(V[..]) == multiset(old(V[..]))
{
    quicksort(V, 0, V.Length);
}

method quicksort(V : array?<int>, c : int, f : int)
    requires V != null && 0 <= c <= f <= V.Length
    modifies V
    ensures segmento_ordenado(V, c, f)
    ensures multiset(V[c..f]) == multiset(old(V[c..f]))
    ensures forall i :: 0 <= i < c ==> V[i] == old(V[i])
    ensures forall i :: f <= i < V.Length ==> V[i] == old(V[i])
{
    if f - c > 1 {
        var pivote : int; 
        pivote := particion(V, c, f);
        quicksort(V, c, pivote);
        quicksort(V, pivote + 1, f);
    }
}

method particion(V : array?<int>, c : int, f : int) returns (pivote : int)
    requires V != null && 0 <= c < f <= V.Length
    modifies V
    ensures c <= pivote < f
    ensures forall i :: c <= i <= pivote ==> V[i] <= V[pivote]
    ensures forall i :: pivote < i < f ==> V[i] >= V[pivote]
    ensures multiset(V[c..f]) == multiset(old(V[c..f]))
    ensures forall i :: 0 <= i < c ==> V[i] == old(V[i])
    ensures forall i :: f <= i < V.Length ==> V[i] == old(V[i])
{
    pivote := c;
    var indice : nat;
    indice := c + 1;
    while indice < f
        invariant c <= pivote < f
        invariant c + 1 <= indice <= f
        invariant forall i :: c + 1 <= i < indice && V[i] < V[pivote] ==> c <= i <= pivote
        invariant multiset(V[c..indice]) == multiset(old(V[c..indice]))
        invariant forall i :: 0 <= i < c ==> V[i] == old(V[i])
        invariant forall i :: f <= i < V.Length ==> V[i] == old(V[i])
    {
        if V[indice] < V[pivote]
        {
            var contador : nat;
            contador := indice - 1;
            var temp : int;
            temp := V[indice];
            V[indice] := V[contador];
            while contador > pivote
                invariant pivote < contador <= indice - 1
                invariant forall i :: contador + 1 <= i <= indice ==> V[i] == old(V[i - 1])
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
