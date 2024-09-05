data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, aa₁₂: [int]int, i₁₃: int ::
      (  0 <= i₁₃
        && i₁₃ <= 100000
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 0 <= i₃
                && i₃ < i₁₃
                 ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                        i₃ < 100000
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₃
                        && aa₁₂[x₄] == __VERIFIER_nondet_int₁₂)))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₃)
                || aa₁₂[x₄] == aa[x₄])
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₃
                 ==> i₃ < 100000))
         ==> i₁₃ < 100000
          || 0 <= 1 + aa₁₂[0]));

goal (forall aa: [int]int, aa₁₂: [int]int, i₁₃: int, a₁₄: int ::
      (  0 <= i₁₃
        && i₁₃ <= 100000
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 0 <= i₃
                && i₃ < i₁₃
                 ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                        i₃ < 100000
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₃
                        && aa₁₂[x₄] == __VERIFIER_nondet_int₁₂)))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₃)
                || aa₁₂[x₄] == aa[x₄])
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₃
                 ==> i₃ < 100000))
        && 0 <= a₁₄
        && 0 <= 1 + aa₁₂[a₁₄]
        && (forall a₇: int ::
              (  0 <= a₇
                && a₇ < a₁₄
                 ==> 0 <= aa₁₂[a₇]))
        && 0 <= aa₁₂[a₁₄]
         ==> i₁₃ < 100000
          || 0 <= 1 + aa₁₂[a₁₄ + 1]));

