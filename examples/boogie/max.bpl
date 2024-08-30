procedure max(a: [int]int, N: int)
    returns (res: int)
    // requires 0 <= N;
{
    var i: int := 0;
    var res: int := a[0];

    while(i < N)
    {
        if(res <= a[i]) {
            res := a[i];
        }
        i := i + 1;
    }
}