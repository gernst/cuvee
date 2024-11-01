procedure test()
{
    var i: int;
    var n: int;

    assume n >= 0;

    top:
        i := 0;

    while(i < n)
        invariant 0 <= i && i <= n;
    {
        goto next, top, out;

        next:
            i := i + 1;
    }

    out:
        assert i <= n;
}