function factorial(n: int): int;

axiom
    forall n: int :: n <= 0 ==> factorial(n) == 1;
axiom
    factorial(1) == 1;
axiom
    forall n: int :: 0 < n ==> factorial(n) == n * factorial(n - 1);

procedure compute(n: int)
    returns (r: int)
    requires 0 <= n;
    ensures r == factorial(n);
{
    var i: int := n;
    r := 1;

    while(0 < i)
        decreases i;
        invariant 0 <= i && i <= n;
        summary final(r) == r*factorial(i);
    {
        r := r * i;
        i := i - 1;
    }
}