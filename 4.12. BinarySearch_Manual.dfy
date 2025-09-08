method BinarySearch(arr: array<int>, target: int) returns (index: int)

    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length - 1 ==> arr[i] <= arr[i + 1]
    ensures -1 <= index < arr.Length
    ensures index == -1 || arr[index] == target
    ensures index != -1 ==> arr[index] == target

{

    var low := 0;
    var high := arr.Length - 1;
    index := -1;

    while low <= high

        invariant 0 <= low <= arr.Length
        invariant -1 <= high < arr.Length
        invariant forall i :: 0 <= i < arr.Length - 1 ==> arr[i] <= arr[i + 1]
        invariant -1 <= index < arr.Length
        invariant index == -1 || arr[index] == target

    {

        var mid := low + (high - low) / 2;

        if arr[mid] == target {

            index := mid;
            return;

        } else if arr[mid] < target {

            low := mid + 1;

        } else {

            high := mid - 1;

        }
        
    }

}