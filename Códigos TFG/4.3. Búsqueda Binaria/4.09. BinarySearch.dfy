method BinarySearch(a: array<int>, x: int) returns (index: int)

{

    var low := 0;
    var high := a.Length - 1;

    while low <= high

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