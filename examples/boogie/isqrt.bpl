procedure isqrt(x: int) returns (i: int)
{
    assume (x >= 0);

    var s: int := 1;
    var u: int := 3;
    i := 0;

    while (s <= x)
        // decreases x - i;
        invariant i*i <= x && s == (i+1)*(i+1) && u == 2*i + 3;
    {
        i := i + 1;
        s := s + u;
        u := u + 2;
    }

    assert i*i <= x && (i+1)*(i+1) > x;
}