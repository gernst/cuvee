procedure innerloop(a: [int]int, n: int)
{
        var l: int;
        var r: int;

        while(l < r)
            decreases r - l;
            invariant 0 <= l && l <= r && r < n;
        {
            if(a[l] > a[l+1]) {
                var al0: int := a[l];
                var al1: int := a[l+1];
                a := a[l+1 := al0][l := al1];
            }
            l := l + 1;
        }
}
