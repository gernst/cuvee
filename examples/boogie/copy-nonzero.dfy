method Test(a: array<int>, b: array<int>)
    requires a.Length >= b.Length
    modifies a
{
    var i := 0;
    var an := 0;

    while i < b.Length
        invariant 0 <= an <= i <= b.Length
        invariant forall x ::
            (0 <= x && x < an)
            ==> (exists i2 :: 0 <= i2 < b.Length &&
                        a[x] == b[i2] && b[i2] != 0)
    {
        if b[i] != 0 {
            a[an] := b[i];
            an := an + 1;
        } else {
            assume forall x ::
                (0 <= x && x < an)
                ==> (exists i2 :: 0 <= i2 < b.Length &&
                            a[x] == b[i2] && b[i2] != 0);
        }
        i := i + 1;
    }
}