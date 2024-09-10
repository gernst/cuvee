data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall a: [int]int, b: [int]int, i₅: int ::
        (exists nondet_int₁₄: int ::
                nondet_int₁₄ == 10
                && i₅ < 100000
                && a[i₅] == nondet_int₁₄
                && b[i₅] == 20)
        || (exists nondet_int₁₄: int ::
                (nondet_int₁₄ == 10
                   ==> false)
                && i₅ < 100000
                && a[i₅] == nondet_int₁₄));

