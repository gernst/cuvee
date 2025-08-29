procedure counter()
{
    var n: int;
    assume 0 <= n;

    var i: int;

    while(i < n) {
        i := i + 1;
    }

    assert i == n;
}