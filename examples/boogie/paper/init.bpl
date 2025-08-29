procedure init(n: int, z: int)
    returns (a: [int]int)
    requires 0 <= n;
    ensures  forall j: int :: 0 <= j && j < n ==> a[j] == z;
{
    var i: int := 0;

    while(i < n) {
        a[i] := z;
        i := i + 1;
    }
}