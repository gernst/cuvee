procedure test(n: int)
    requires 0 <= n;
{
    var i: int := 1;

    while(i <= n) {
        i := i + 1;
    }

    assert i == n;
}