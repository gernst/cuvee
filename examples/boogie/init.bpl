procedure init(z: int, n: int)
    returns (a: [int]int)
    requires 0 <= n;
    ensures  forall k: int :: 0 <= k && k < n ==> a[k] == z;
{
    var i: int := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;

        summary forall k: int ::
            (forall i_: int :: i <= i_ ==> i_ != k)
                 ==> final(a[k]) == a[k];
    {
        a := a[i := z];
        i := i + 1;
    }
}
