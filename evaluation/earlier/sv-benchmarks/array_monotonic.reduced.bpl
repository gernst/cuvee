data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall a: [int]int, b: [int]int, i₅: int ::
        (exists __VERIFIER_nondet_int₁₄: int ::
                __VERIFIER_nondet_int₁₄ == 10
                && i₅ < 100000
                && a[i₅] == __VERIFIER_nondet_int₁₄
                && b[i₅] == 20)
        || (exists __VERIFIER_nondet_int₁₄: int ::
                (__VERIFIER_nondet_int₁₄ == 10
                   ==> false)
                && i₅ < 100000
                && a[i₅] == __VERIFIER_nondet_int₁₄));

