procedure init(n: int, b: [int]int)
    returns (a: [int]int)
    requires 0 <= n;
    ensures  forall j: int :: 0 <= j && j < n ==> a[j] == b[j];
{
    var i: int := 0;

    while(i < n) {
        a[i] := b[i];
        i := i + 1;
    }
}
