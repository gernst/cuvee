procedure abs(x: int)
    returns (y: int)
{
    if(x >= 0) {
        // y := x;
    } else {
        y := -x;
    }

    x := x + 7;
}

procedure test(x: int)
    ensures true;
{
    var y: int := 23;
    x := x + 1;
    var z: int;
    z := call abs(x);
    assert z == (if x > 0 then x else -x);
}