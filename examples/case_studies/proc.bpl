procedure max(x: int, y: int) returns (z: int) {
    assume x > y;
    z := x;
    assert z > y;

    var a: int, b: int;

    var a0: int, b0: int := a, b;
    assume a >= 0;

    while(a > 0)
        decreases a;
        invariant a >= 0 && a + b == a0 + b0;
    {
        a := a - 1;
        b := b + 1;
    }

    assert b == a0 + b0;
}

