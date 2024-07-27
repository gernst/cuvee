procedure init(z: int, n: int)
    returns (a: [int]int)
    requires 0 <= n;
    ensures  forall k: int :: 0 <= k && k < n ==> a[k] == z;
{
    var i: int := 0;

    while(i < n)
    {
        a := a[i := z];
        i := i + 1;
    }

    var j: int := 0;
    while (j < n)
    {
        assert a[j] == z;
        j := j + 1;
    }
}
