
procedure find(x: int, a: [int]int, n: int)
    returns (i: int)
    requires 0 <= n;
    ensures  0 <= i && (i < n ==> a[i] == x);
    ensures  forall k: int :: 0 <= k && k < i ==> a[k] != x;
{
    i := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;
    {
        if(a[i] == x) { break; }
        i := i + 1;
    }
}
