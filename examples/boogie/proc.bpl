procedure test(x: int, y: int)
    returns (z: int)
{
    assume x > y;
    z := x;
    assert z > y;
}

procedure contract(x: int, y: int)
    returns (z: int)
    requires x > y;
    ensures  z > y;
{
    z := x;
    y := x;
}

procedure loop1() {
    var a: int, b: int;

    var a0: int, b0: int := a, b;
    assume a >= 0;

    while(a > 0)
        decreases a;
        invariant a >= 0;
        invariant a + b == a0 + b0;
    {
        a := a - 1;
        b := b + 1;
    }

    assert b == a0 + b0;
}

procedure summary1() {
    var a: int, b: int;

    var a0: int, b0: int := a, b;
    assume a >= 0;

    while(a > 0)
        decreases a;
        summary   final(b) == a + b;
        invariant a >= 0;
    {
        a := a - 1;
        b := b + 1;
    }

    assert b == a0 + b0;
}

function contains(x: int, a: [int]int, i: int, n: int): bool {
    exists k: int :: i <= k && k < n && a[k] == x
}

procedure lsearch(x: int, a: [int]int, n: int)
{
    assume 0 <= n;

    var r: bool := false;
    var i: int  := 0;

    // observation: we do not even need summaries in the backend, we can avoid the quantifier if
    // we let final(_) denote some arbitrary but *fixed* final state,
    // but that does not *force* us to prove that the summary is preserved (i.e. implication premise can just fail silently)
    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n && !r;
        // invariant initial(i) <= i && earlier(i) < i && i < later(i);
        // summary   final(r) <==> contains(x, a, i, n);
        // for a in mod:
        //    invariant old(a[k])   == a[k] if earlier(a[k] == a'[k]) for all earlier transitions
        //    summary   final(a[k]) == a[k] if later(a[k] == a'[k]) for all later transitions

        summary   final(r) <==> contains(x, a, i, n);
    {
        if(x == a[i]) {
            r := true;
            break;
        }
        
        i := i + 1;
    }

    assert r <==> contains(x, a, 0, n);
}

procedure copy(a: [int]int, n: int) returns (b: [int]int)
{
    assume 0 <= n;
    var i: int  := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;
        // transition invariant i < i' therefore *after* one iteration we get i <= i' + 1 i.e. i < i'
        // cf. Rybalchenko & Podelski, LICS 04

        // proof rule: R <= T and T;R <= T
        // moreover if T is transition invariant then
        // I + { s' | I(s) /\ T(s,s') }
        // is regular invariant, i.e., all T successors from some invariant

        // modifies clauses: ex T predecessor in current state such that array is modified in that iteration
    {
        b := b[i := a[i]];
        i := i + 1;

        // we want a formula like i < i' that relates two arbitrary iterations
        // such that we can say that all indices from prior iterations that are modified are def. smaller
        // we *should* be able to compute this by accelleration or abstract interpretation
    }


}