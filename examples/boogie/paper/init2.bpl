procedure init(n: int, z: int, c: int)
    returns (a: [int]int)
    requires 0 <= n;
    ensures  forall l: int :: c <= l && l < n + c ==> a[l] == z;
    // ensures  forall l: int :: 0 <= l && l < n ==> a[l + c] == z;
{
    var i: int := 0;

    while(i < n) {
        a[i + c] := z;
        i := i + 1;
    }
}
