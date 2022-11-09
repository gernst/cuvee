function contains(x: int, a: [int]int, i: int, n: int): bool {
    exists k: int ::
        i <= k && k < n && a[k] == x
}

function sorted(a: [int]int, i: int, n: int): bool {
    forall j: int, k: int ::
        i <= j && j <= k && k < n ==> a[j] <= a[k]
}

procedure bsearch_invariant(x: int, a: [int]int, n: int)
    returns (found: bool)
    requires 0 < n && sorted(a, 0, n);
    ensures found <==> contains(x, a, 0, n);
{
    var l: int := 0;
    var r: int := n;

    while(l < r)
        decreases r - l;
        invariant 0 <= l && l <= r && r <= n;
        invariant !contains(x, a, 0, l);
        invariant !contains(x, a, r, n);
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
    
    found := false;
}

procedure bsearch_summary(x: int, a: [int]int, n: int)
    returns (found: bool)
    requires 0 < n && sorted(a, 0, n);
    ensures found <==> contains(x, a, 0, n);
{
    var l: int := 0;
    var r: int := n;
    
    found := false;

    while(l < r)
        decreases r - l;
        invariant 0 <= l && l <= r && r <= n && !found;
        summary   final(found) <==> contains(x, a, l, r);
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
