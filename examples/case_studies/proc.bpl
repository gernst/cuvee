procedure test(x: int, y: int) returns (z: int) {
    assume x > y;
    z := x;
    assert z > y;
}

procedure loop1() {
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

procedure summary1() {
    var a: int, b: int;

    var a0: int, b0: int := a, b;
    assume a >= 0;

    while(a > 0)
        decreases a;
        invariant a >= 0;
        summary   b == old(a + b);
    {
        a := a - 1;
        b := b + 1;
    }

    assert b == a0 + b0;
}

function contains(x: int, a: [int]int, i: int, n: int): bool {
    exists k: int :: i <= k && k < n && a[k] == x
}

procedure lsearch(x: int, a: [int]int, n: int)
{
    assume 0 <= n;

    var r: bool := false;
    var i: int  := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n && !r;
        summary   r <==> old(contains(x, a, i, n));
    {
        if(x == a[i]) {
            r := true;
            break;
        }
        
        i := i + 1;
    }

    assert r <==> contains(x, a, 0, n);
}

procedure copy(a: [int]int, n: int) returns (b: [int]int)
{
    assume 0 <= n;
    var i: int  := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;
    {
        b := b[i := a[i]];
        i := i + 1;
    }


}