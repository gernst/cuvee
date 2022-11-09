procedure zero(b: [int]int, n: int)
{
    assume 0 <= n;
    var i: int := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n &&
                  forall k: int :: 0 <= k && k < i ==> b[k] == 0;
    {
        b := b[i := 0];
        i := i + 1;
    }

    assert forall k: int ::
        0 <= k && k < n ==> b[k] == 0;
}

procedure zero_sm(b: [int]int, n: int)
{
    assume 0 <= n;
    var i: int := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;
        summary (forall k: int :: i <= k && k < n ==> final(b[k]) == 0) &&
                (forall k: int :: 0 <= k && k < i ==> final(b[k]) == b[k]);
    {
        b := b[i := 0]; // b[i] is modified in any iteration
        i := i + 1;
    }

    assert forall k: int ::
        0 <= k && k < n ==> b[k] == 0;
}


procedure shift(b: [int]int, n: int)
{
    assume 0 <= n;
    var a: [int]int := b;
    var i: int := 0;

    // needs framing if we replace a by a resp. old(b) below
    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n &&
                  forall k: int :: 0 <= k && k < i ==> b[k] == a[k + 1];
    {
        b := b[i := a[i + 1]];
        i := i + 1;
    }

    assert forall k: int ::
        0 <= k && k < n ==> b[k] == a[k + 1];
}
