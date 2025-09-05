procedure counter()
{
    var x1: int := 0;
    var x2: int := 0;

    while(x1 > 0 && x2 > 0) {
        x1 := x1 - 1;
        x2 := x2 + 1;
    }

    assert x1 <= 0;
}
