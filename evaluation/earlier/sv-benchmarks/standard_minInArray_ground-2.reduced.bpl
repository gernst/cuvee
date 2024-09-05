data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, a₁₄: [int]int, i₁₅: int, min₁₆: int, i₁₇: int, x₁₈: int ::
      (  0 <= i₁₅
        && i₁₅ <= 100000
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 0 <= i₃
                && i₃ < i₁₅
                 ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                        i₃ < 100000
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₅
                        && a₁₄[x₄] == __VERIFIER_nondet_int₁₂)))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₅)
                || a₁₄[x₄] == a[x₄])
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₅
                 ==> i₃ < 100000))
        && 0 <= i₁₇
        && i₁₇ <= 100000
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₇
                 ==> i₈ < 100000))
        && 0 <= x₁₈
        && x₁₈ <= 100000
        && (forall x₁₂: int ::
              (  0 <= x₁₂
                && x₁₂ < x₁₈
                 ==> x₁₂ < 100000))
        && x₁₈ < 100000
         ==> i₁₇ < 100000
          || i₁₅ < 100000
          || min₁₆ <= a₁₄[x₁₈]));

