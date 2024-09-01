data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, a₁₄: [int]int, j₁₅: int, max₁₆: int, i₁₇: int, x₁₈: int ::
      (  0 <= j₁₅
        && j₁₅ <= 100000
        && (forall x₄: int, j₃: int ::
              (  x₄ == j₃
                && 0 <= j₃
                && j₃ < j₁₅
                 ==> (exists __VERIFIER_nondet_int₁₂: int, j₃: int ::
                        j₃ < 100000
                        && x₄ == j₃
                        && 0 <= j₃
                        && j₃ < j₁₅
                        && a₁₄[x₄] == __VERIFIER_nondet_int₁₂)))
        && (forall x₄: int ::
                (exists j₃: int ::
                        x₄ == j₃
                        && 0 <= j₃
                        && j₃ < j₁₅)
                || a₁₄[x₄] == a[x₄])
        && (forall j₃: int ::
              (  j₃ <= j₃
                && 0 <= j₃
                && j₃ < j₁₅
                 ==> j₃ < 100000))
        && 0 <= i₁₇
        && i₁₇ <= 100000
        && (forall i₈: int ::
              (  i₈ <= i₈
                && 0 <= i₈
                && i₈ < i₁₇
                 ==> i₈ < 100000))
        && 0 <= x₁₈
        && x₁₈ <= 100000
        && (forall x₁₂: int ::
              (  x₁₂ <= x₁₂
                && 0 <= x₁₂
                && x₁₂ < x₁₈
                 ==> x₁₂ < 100000))
        && x₁₈ < 100000
         ==> i₁₇ < 100000
          || j₁₅ < 100000
          || a₁₄[x₁₈] <= max₁₆));

