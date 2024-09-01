data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall b: [int]int, x₇: int, i₅: int ::
      (x₇ == i₅
         ==> (exists __VERIFIER_nondet_int₁₄: int, i₃₃: int ::
                __VERIFIER_nondet_int₁₄ == 10
                && i₃₃ < 100000
                && x₇ == i₃₃
                && b[x₇] == 20)));

goal (forall i₅: int ::
      i₅ < 100000);

