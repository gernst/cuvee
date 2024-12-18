procedure sum(a: [int]int, n: int)
    requires 0 <= n;
{
    var i: int;
    var s1: int, s2: int;

    i, s1 := 0, 0;
    while(i < n) {
        i, s1 := i + 1, s1 + a[i];
    }

    i, s2 := 0, 0;
    while(i < n) {
        i, s2 := i + 1, s2 + a[i];
    }

    assert s1 == s2;
}
