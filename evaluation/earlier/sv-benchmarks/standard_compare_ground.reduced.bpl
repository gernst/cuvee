data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, a₁₈: [int]int, b₁₉: [int]int, j₂₀: int, rv₂₁: int, i₂₂: int, x₂₃: int ::
      (  0 <= j₂₀
        && j₂₀ <= 100000
        && (forall x₆: int, j₅: int ::
              (  x₆ == j₅
                && 0 <= j₅
                && j₅ < j₂₀
                 ==> (exists __VERIFIER_nondet_int₁₃: int, j₅: int ::
                        j₅ < 100000
                        && x₆ == j₅
                        && 0 <= j₅
                        && j₅ < j₂₀
                        && a₁₈[x₆] == __VERIFIER_nondet_int₁₃)))
        && (forall x₆: int ::
                (exists j₅: int ::
                        x₆ == j₅
                        && 0 <= j₅
                        && j₅ < j₂₀)
                || a₁₈[x₆] == a[x₆])
        && (forall x₇: int, j₅: int ::
              (  x₇ == j₅
                && 0 <= j₅
                && j₅ < j₂₀
                 ==> (exists __VERIFIER_nondet_int₂₄: int, j₅: int ::
                        j₅ < 100000
                        && x₇ == j₅
                        && 0 <= j₅
                        && j₅ < j₂₀
                        && b₁₉[x₇] == __VERIFIER_nondet_int₂₄)))
        && (forall x₇: int ::
                (exists j₅: int ::
                        x₇ == j₅
                        && 0 <= j₅
                        && j₅ < j₂₀)
                || b₁₉[x₇] == b[x₇])
        && (forall j₅: int ::
              (  0 <= j₅
                && j₅ < j₂₀
                 ==> j₅ < 100000))
        && 0 <= i₂₂
        && i₂₂ <= 100000
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₂₂
                 ==> i₁₂ < 100000))
        && 0 <= x₂₃
        && x₂₃ <= 100000
        && (forall x₁₆: int ::
              (  0 <= x₁₆
                && x₁₆ < x₂₃
                 ==> x₁₆ < 100000))
        && x₂₃ < 100000
         ==> rv₂₁ == 0
          || i₂₂ < 100000
          || j₂₀ < 100000
          || a₁₈[x₂₃] == b₁₉[x₂₃]));

