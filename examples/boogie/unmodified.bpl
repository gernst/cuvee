function I(a1: [int]int, i1: int, a2: [int]int, i2: int, n: int): bool {
    forall k: int ::
        i1 <= k && k < i2 ==> a2[k] == 0
}

function U(a1: [int]int, i1: int, a2: [int]int, i2: int, n: int): bool {
    forall k: int ::
        k < i1 ==> a2[k] == a1[k]
}

lemma forall a1: [int]int, i1: int, a2: [int]int, i2: int, n: int ::
    I(a1, i1, a2, i2, n)
        <==>  forall k: int ::
                i1 <= k && k < i2 ==> a2[k] == 0;

lemma forall a1: [int]int, i1: int, a2: [int]int, i2: int, n: int ::
    U(a1, i1, a2, i2, n)
        <==>  forall k: int ::
                k < i1 ==> a2[k] == a1[k];

procedure unmodified(a: [int]int, n: int)
{
    assume 0 <= n;
    var i: int := 0;
    var k: int;
    var b: [int]int := a;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;

        // invariant I(old(a), old(i), a, i, n);

        // This summary can be constructed automatically from a transition invariant old(i) <= i
        // and by noticing that the array is modified at exactly i == k
        // summary U(old(a), old(i), a, i, n);

        invariant forall k: int ::
            (forall i_ : int :: 0 <= i_ && i_ < i ==> k != i_) // !(0 <= k && k < i)
                ==> a[k] == old(a[k]);
    {
        a := a[i := 0];
        i := i + 1;
    }

    // assert false;
}