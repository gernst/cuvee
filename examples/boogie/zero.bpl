procedure zero(b: [int]int, n: int)
{
    assume 0 <= n;
    var i: int := 0;

    while(i < n)
        decreases n - i;
        invariant // 0 <= i && i <= n &&
                  forall k: int :: 0 <= k && k < i
                        ==> b[k] == 0;
    {
        b := b[i := 0];
        i := i + 1;
    }

    assert forall k: int ::
        0 <= k && k < n ==> b[k] == 0;
}