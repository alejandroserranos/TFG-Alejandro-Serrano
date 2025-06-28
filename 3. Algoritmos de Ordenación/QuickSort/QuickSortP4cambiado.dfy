method ordenar_quicksort(V : array?<int>)
    requires V != null
    modifies V
{
    quicksort(V, 0, V.Length) ;
}

predicate segmento_ordenado(V : array?<int>, c : int, f : int)
    reads V
    requires V != null && 0 <= c <= f <= V.Length
{
    forall j, k :: c <= j < k < f ==> V[j] <= V[k]
}

method quicksort(V : array?<int>, c : int, f : int)
    requires V != null && 0 <= c <= f <= V.Length
    modifies V
    decreases f - c
{
    if f - c > 1 {
        var pivote : int ; 
        pivote := particion(V, c, f) ;
        quicksort(V, c, pivote) ;
        quicksort(V, pivote + 1, f) ;
    } else {
        return ;  
    }  
}

method particion(V : array?<int>, c : int, f : int) returns (pivote : int)
    requires V != null && 0 <= c < f <= V.Length
    modifies V
    ensures c <= pivote < f
{
    pivote := c ;
    var indice : nat ;
    indice := c + 1 ;
    while indice < f
        invariant c <= pivote < indice <= f
        decreases f - indice
    {
        if V[indice] < V[pivote]
        {
            var contador : nat ;
            contador := indice - 1 ;
            var temp : int ;
            temp := V[indice] ;
            V[indice] := V[contador] ;
            while contador > pivote
                decreases contador - pivote
            {
                V[contador + 1] := V[contador] ;
                contador := contador - 1 ;
            }
            V[pivote + 1] := V[pivote] ;
            pivote        := pivote + 1 ;
            V[pivote - 1] := temp ; 
        }
        indice := indice + 1 ;
    }
}