procedure main()
{
    var n: int;
    assume 0 <= n;

    var i: int, j: int := 0, 0;

    while(i < n) {
        i, j := j + 1, i + 1;
    }

    assert i == j;
}
