data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int, a: [int]int, b: [int]int, j₁₉: int, i₂₀: int, b₂₁: [int]int, i₂₂: int, k₂₃: int, i₂₄: int ::
      (  __VERIFIER_nondet_int₁ < 10000
        && -10000 < __VERIFIER_nondet_int₁
        && __VERIFIER_nondet_int₂ < 10000
        && -10000 < __VERIFIER_nondet_int₂
        && 0 <= i₂₀
        && (forall j₈: int, i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₀
                 ==> a[i₉] < j₈
                    && a[i₉] < 10000
                    && -10000 < a[i₉]
                    && i₉ < __VERIFIER_nondet_int₂
                  ||   (a[i₉] < j₈
                       ==> false)
                    && a[i₉] < 10000
                    && -10000 < a[i₉]
                    && i₉ < __VERIFIER_nondet_int₂))
        && 0 <= i₂₂
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₂₂
                 ==> i₁₂ < __VERIFIER_nondet_int₂
                  && b₂₁[i₁₂] == a[i₁₂] + -j₁₉))
        && (forall i₁₂: int ::
                  0 <= i₁₂
                  && i₁₂ < i₂₂
                || b₂₁[i₁₂] == b[i₁₂])
        && 0 <= i₂₄
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₂₄
                 ==> i₁₆ < __VERIFIER_nondet_int₂))
         ==> i₂₄ < __VERIFIER_nondet_int₂
          || i₂₂ < __VERIFIER_nondet_int₂
          || i₂₀ < __VERIFIER_nondet_int₂
          || 0 <= k₂₃));

