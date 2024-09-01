data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int, a: [int]int, acopy: [int]int, x₇: int, i₆: int ::
      (  1 < __VERIFIER_nondet_int₁
        && __VERIFIER_nondet_int₁ < 1073741823
        && (x₇ == i₆
           ==> 0 <= i₆
            && i₆ < 0)
        &&   x₇ == i₆
          || x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆
         ==> (exists i₂₅: int ::
                i₂₅ < __VERIFIER_nondet_int₁
                && if(x₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < 0 && acopy[x₇] == a[i₂₅] else x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₂₅ && acopy[x₇] == a[1 + 2 * __VERIFIER_nondet_int₁ + -i₂₅])));

