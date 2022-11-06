type elem;

function contains(x: elem, a: [int]elem, i: int, n: int): bool {
    exists k: int ::
        i <= k && k < n && a[k] == x
}

procedure lsearch_invariant(x: elem, a: [int]elem, n: int)
    returns (found: bool)
    requires 0 <= n;
    ensures found <==> contains(x, a, 0, n);
{
    var i: int := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;
        invariant !contains(x, a, 0, i);
    {
        if(a[i] == x) {
            found := true;
            return;
        }

        i := i + 1;
    }

    // we assign the variable found here instead of in the beginning
    // to avoid tracking that found remains false unless we hit the exit case
    found := false;
}

procedure lsearch_summary(x: elem, a: [int]elem, n: int)
    returns (found: bool)
    requires 0 <= n;
    ensures found <==> contains(x, a, 0, n);
{
    var i: int := 0;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;

        // dually to the invariant we reason about the residual range,
        // which is *easier* to generalize automatically from i == 0 initially,
        // however, in this variant, we need to know that found == false finally,
        // such that the postcondition collapses as shown:
        summary !contains(x, a, old(i), n);
    {
        if(a[i] == x) {
            found := true;
            // return immediately. note that the summary is *not* established here,
            // showcasing that the verification conditions are liberal regarding
            // whether the summary is used in abrupt loop termination cases at all
            return;
        }

        i := i + 1;
    }

    found := false;
}

procedure lsearch_summary_break(x: elem, a: [int]elem, n: int)
    returns (found: bool)
    requires 0 <= n;
    ensures found <==> contains(x, a, 0, n);
{
    var i: int := 0;
    found := false;

    while(i < n)
        decreases n - i;
        // in this variant we set found to false upfront,
        // such that we have to explicitly track this fact in the invariant
        invariant 0 <= i && i <= n && !found;
        // as a consequence, the summary becomes very similar to the postcondition
        summary found <==> contains(x, a, old(i), n);
    {
        if(a[i] == x) {
            // note we break here:
            found := true;
            break;
        }

        i := i + 1;
    }
}

