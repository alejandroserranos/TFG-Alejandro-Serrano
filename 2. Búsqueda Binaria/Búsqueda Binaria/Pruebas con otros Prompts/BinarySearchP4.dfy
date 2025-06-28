method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires a != null
    requires a.Length >= 0
    requires forall i: int :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]  // el array debe estar ordenado
    ensures 0 <= index < a.Length ==> a[index] == x  // si se devuelve un índice válido, debe contener x
    ensures index == -1 ==> forall i: int :: 0 <= i < a.Length ==> a[i] != x  // si devuelve -1, x no está
    ensures index != -1 ==> a[index] == x // redundante pero útil
{
    var low := 0;
    var high := a.Length - 1;

    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant forall i: int :: 0 <= i < low ==> a[i] < x  // todos los descartados por debajo son < x
        invariant forall i: int :: high < i < a.Length ==> a[i] > x  // descartados por arriba son > x
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
