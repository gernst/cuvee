procedure main(a: [int]int, m: int)
    returns (b: [int]int, n: int)
    requires 0 <= m;
{
    var i: int := 0;
    var s: int := 0;

    while(i < m)
    {
        if(a[i] >= 0) {
            b[n] := a[i];
            s := s + a[i];
            n := n + 1;
        }

        i := i + 1;
    }
}
