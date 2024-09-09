data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int, a: [int]int, acopy: [int]int, acopy₁₁: [int]int, i₁₂: int, i₆: int ::
      (  1 < __VERIFIER_nondet_int₁
        && __VERIFIER_nondet_int₁ < 1073741823
        && 0 <= i₁₂
        && (forall i₈₁: int ::
              (  0 <= i₈₁
                && i₈₁ < i₁₂
                 ==> i₈₁ < __VERIFIER_nondet_int₁
                  && acopy₁₁[i₈₁] == a[i₈₁]
                  &&   1 + 2 * __VERIFIER_nondet_int₁ + -i₈₁ == i₈₁
                    || acopy₁₁[1 + 2 * __VERIFIER_nondet_int₁ + -i₈₁] == a[1 + 2 * __VERIFIER_nondet_int₁ + -i₈₁]))
        && (forall i₈₂: int ::
                  0 <= i₈₂
                  && i₈₂ < i₁₂
                ||   acopy₁₁[i₈₂] == acopy[i₈₂]
                  && acopy₁₁[1 + 2 * __VERIFIER_nondet_int₁ + -i₈₂] == acopy[1 + 2 * __VERIFIER_nondet_int₁ + -i₈₂])
        && i₁₂ < __VERIFIER_nondet_int₁
         ==> i₆ < i₁₂ + 1
          || acopy₁₁[2 * __VERIFIER_nondet_int₁ - i₁₂ + 1 := a[2 * __VERIFIER_nondet_int₁ - i₁₂ + 1]][i₁₂ := a[i₁₂]][i₆] == acopy[i₆]));

goal (forall __VERIFIER_nondet_int₁: int, a: [int]int, acopy: [int]int, acopy₁₁: [int]int, i₁₂: int, i₆: int ::
      (  1 < __VERIFIER_nondet_int₁
        && __VERIFIER_nondet_int₁ < 1073741823
        && 0 <= i₁₂
        && (forall i₈₉: int ::
              (  0 <= i₈₉
                && i₈₉ < i₁₂
                 ==> i₈₉ < __VERIFIER_nondet_int₁
                  && acopy₁₁[i₈₉] == a[i₈₉]
                  &&   1 + 2 * __VERIFIER_nondet_int₁ + -i₈₉ == i₈₉
                    || acopy₁₁[1 + 2 * __VERIFIER_nondet_int₁ + -i₈₉] == a[1 + 2 * __VERIFIER_nondet_int₁ + -i₈₉]))
        && (forall i₉₀: int ::
                  0 <= i₉₀
                  && i₉₀ < i₁₂
                ||   acopy₁₁[i₉₀] == acopy[i₉₀]
                  && acopy₁₁[1 + 2 * __VERIFIER_nondet_int₁ + -i₉₀] == acopy[1 + 2 * __VERIFIER_nondet_int₁ + -i₉₀])
        && i₁₂ < __VERIFIER_nondet_int₁
         ==> i₆ < i₁₂ + 1
          || acopy₁₁[2 * __VERIFIER_nondet_int₁ - i₁₂ + 1 := a[2 * __VERIFIER_nondet_int₁ - i₁₂ + 1]][i₁₂ := a[i₁₂]][1 + 2 * __VERIFIER_nondet_int₁ + -i₆] == acopy[1 + 2 * __VERIFIER_nondet_int₁ + -i₆]));

goal (forall __VERIFIER_nondet_int₁: int, a: [int]int, acopy: [int]int, acopy₁₁: [int]int, i₁₂: int, i₁₃: int ::
      (  1 < __VERIFIER_nondet_int₁
        && __VERIFIER_nondet_int₁ < 1073741823
        && 0 <= i₁₂
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₂
                 ==> i₆ < __VERIFIER_nondet_int₁
                  && acopy₁₁[i₆] == a[i₆]
                  &&   1 + 2 * __VERIFIER_nondet_int₁ + -i₆ == i₆
                    || acopy₁₁[1 + 2 * __VERIFIER_nondet_int₁ + -i₆] == a[1 + 2 * __VERIFIER_nondet_int₁ + -i₆]))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₂
                ||   acopy₁₁[i₆] == acopy[i₆]
                  && acopy₁₁[1 + 2 * __VERIFIER_nondet_int₁ + -i₆] == acopy[1 + 2 * __VERIFIER_nondet_int₁ + -i₆])
        && 0 <= i₁₃
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₁₃
                 ==> i₉ < 2 * __VERIFIER_nondet_int₁))
        && i₁₃ < 2 * __VERIFIER_nondet_int₁
         ==> i₁₂ < __VERIFIER_nondet_int₁
          || acopy₁₁[i₁₃] == a[i₁₃]));

