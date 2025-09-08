predicate isSorted(a : array?<int>)

    requires a != null
    reads a

{

    forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]

}


method SelectionSort(a: array<int>) 

{

  var n := 0;

  while (n != a.Length)

  {

    var mindex := n;
    var m := n + 1;

    while (m != a.Length)

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