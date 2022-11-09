function is_max(x: int, a: [int]int, i: int, n: int): bool {
    forall k: int ::
        i <= k && k < n ==> a[k] <= x
}

function contains(x: int, a: [int]int, i: int, n: int): bool {
    exists k: int ::
        i <= k && k < n && a[k] == x
}

procedure findmax(a: [int]int, n: int)
    returns (x: int)
    requires 0 < n;
    ensures  contains(x, a, 0, n);
    ensures  is_max(x, a, 0, n);
{
    var l: int := 0;
    var r: int := n;

    while(l < r-1)
        decreases r - l;
        invariant 0 <= l && l <= r-1 && r <= n;
    {
        if(a[l] < a[r-1]) { l := l + 1; }
        else              { r := r - 1; }
    }

    x := a[l];
}

function sorted(a: [int]int, i: int, n: int): bool {
    forall j: int, k: int ::
        i <= j && j <= k && k < n ==> a[j] <= a[k]
}

procedure bsearch(x: int, a: [int]int, n: int)
    returns (found: bool)
    requires 0 < n && sorted(a, 0, n);
    ensures  found <==> contains(x, a, 0, n);
{
    var l: int := 0;
    var r: int := n;
    
    found := false;

    while(l < r)
        decreases r - l;
        invariant 0 <= l && l <= r && r <= n && !found;
        // invariant !contains(x, a, 0, l);
        // invariant !contains(x, a, r, n);
        // invariant contains(x, a, 0, n) <==> contains(x, a, l, r);
        // summary   final(found) <==> contains(x, a, l, r);
    {
        var m: int := (l + r) / 2;

        if(x > a[m]) {
            l := m + 1;
        } else if(x < a[m]) {
            r := m;
        } else {
            found := true;
            return;
        }
    }
}
