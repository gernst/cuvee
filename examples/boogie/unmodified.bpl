
procedure unmodified(a: [int]int, n: int)
{
    assume 0 <= n;
    var i: int := 0;
    var k: int;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;

        // This summary can be constructed automatically from a transition invariant i < i'
        // and by noticing that the array is modified at exactly i == k
        summary   forall k: int ::
                      (forall i1: int :: old(i) < i1 ==> i1 != k)
                           && old(i != k) ==> a[k] == old(a[k]);
    {
        a := a[i := 0];
        i := i + 1;
    }
}

function T(i: int, i_: int): bool {
    i <= i_
}

function phi(i: int, k: int): bool {
    i == k
}

// here schematically:
procedure unmodified2(a: [int]int, n: int)
{
    assume 0 <= n;
    var i: int := 0;
    var k: int;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;
        summary   forall k: int :: // this index is not modified now and also not later
                      (forall i1: int :: T(old(i), i1) ==> !phi(i1, k))
                           ==> a[k] == old(a[k]);
    {
        a := a[i := 0];
        i := i + 1;
    }

    assert forall k: int ::
        a[k] == 0;
}