function sorted(a: [int]int, l: int, r: int): bool {
    forall i: int, j: int :: l <= i && i <= j && j < r ==>
        a[i] <= a[j]
}

function max(a: [int]int, l: int, r: int): int;

axiom forall a: [int]int, l: int, r: int ::
    l < r ==> l <= max(a, l, r) && max(a, l, r) < r;

axiom forall a: [int]int, l: int, k: int, r: int ::
    l <= k && k < r ==> a[k] <= a[max(a, l, r)];

procedure bubblesort(a: [int]int, n: int)
{
    assume 0 < n;

    var r: int := n - 1;

    while(r > 0)
        decreases r;
        invariant 0 <= r && r < n;
    {
        var l: int := 0;

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

        r := r - 1;
    }
}