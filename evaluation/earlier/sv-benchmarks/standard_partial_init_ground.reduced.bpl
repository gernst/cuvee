data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₄: [int]int, B₂₅: [int]int, i₂₆: int, C₂₇: [int]int, j₂₈: int, i₂₉: int, x₃₀: int ::
      (  0 <= i₂₆
        && i₂₆ <= 100000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₂₆
                 ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₆
                        && A₂₄[x₈] == __VERIFIER_nondet_int₁₅)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₆)
                || A₂₄[x₈] == A[x₈])
        && (forall x₉: int, i₇: int ::
              (  x₉ == i₇
                && 0 <= i₇
                && i₇ < i₂₆
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 100000
                        && x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₆
                        && B₂₅[x₉] == __VERIFIER_nondet_int₂₆)))
        && (forall x₉: int ::
                (exists i₇: int ::
                        x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₆)
                || B₂₅[x₉] == B[x₉])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₂₆
                 ==> i₇ < 100000))
        && 0 <= j₂₈
        && 0 <= i₂₉
        && i₂₉ <= 100000
        && (forall x₁₅: int, j₁₃: int ::
              (  x₁₅ == j₁₃
                && 0 <= j₁₃
                && j₁₃ < j₂₈
                 ==> (exists j₁₃: int, i₁₄: int ::
                        A₂₄[i₁₄] == B₂₅[i₁₄]
                        && i₁₄ < 100000
                        && x₁₅ == j₁₃
                        && 0 <= j₁₃
                        && j₁₃ < j₂₈
                        && 0 <= i₁₄
                        && i₁₄ < i₂₉
                        && C₂₇[x₁₅] == i₁₄)))
        && (forall x₁₅: int ::
                (exists j₁₃: int ::
                        x₁₅ == j₁₃
                        && 0 <= j₁₃
                        && j₁₃ < j₂₈)
                || C₂₇[x₁₅] == C[x₁₅])
        && (forall j₁₃: int, i₁₄: int ::
              (  j₁₃ <= j₁₃
                && i₁₄ <= i₁₄
                && 0 <= j₁₃
                && j₁₃ < j₂₈
                && 0 <= i₁₄
                && i₁₄ < i₂₉
                 ==> i₁₄ < 100000))
        && 0 <= x₃₀
        && x₃₀ <= j₂₈
        && (forall x₂₀: int ::
              (  x₂₀ <= x₂₀
                && 0 <= x₂₀
                && x₂₀ < x₃₀
                 ==> x₂₀ < j₂₈))
        && x₃₀ < j₂₈
         ==> i₂₉ < 100000
          || i₂₆ < 100000
          || C₂₇[x₃₀] <= x₃₀ + i₂₉ - j₂₈));

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₄: [int]int, B₂₅: [int]int, i₂₆: int, C₂₇: [int]int, j₂₈: int, i₂₉: int, x₃₀: int, x₃₁: int ::
      (  0 <= i₂₆
        && i₂₆ <= 100000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₂₆
                 ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₆
                        && A₂₄[x₈] == __VERIFIER_nondet_int₁₅)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₆)
                || A₂₄[x₈] == A[x₈])
        && (forall x₉: int, i₇: int ::
              (  x₉ == i₇
                && 0 <= i₇
                && i₇ < i₂₆
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 100000
                        && x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₆
                        && B₂₅[x₉] == __VERIFIER_nondet_int₂₆)))
        && (forall x₉: int ::
                (exists i₇: int ::
                        x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₆)
                || B₂₅[x₉] == B[x₉])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₂₆
                 ==> i₇ < 100000))
        && 0 <= j₂₈
        && 0 <= i₂₉
        && i₂₉ <= 100000
        && (forall x₁₅: int, j₁₃: int ::
              (  x₁₅ == j₁₃
                && 0 <= j₁₃
                && j₁₃ < j₂₈
                 ==> (exists j₁₃: int, i₁₄: int ::
                        A₂₄[i₁₄] == B₂₅[i₁₄]
                        && i₁₄ < 100000
                        && x₁₅ == j₁₃
                        && 0 <= j₁₃
                        && j₁₃ < j₂₈
                        && 0 <= i₁₄
                        && i₁₄ < i₂₉
                        && C₂₇[x₁₅] == i₁₄)))
        && (forall x₁₅: int ::
                (exists j₁₃: int ::
                        x₁₅ == j₁₃
                        && 0 <= j₁₃
                        && j₁₃ < j₂₈)
                || C₂₇[x₁₅] == C[x₁₅])
        && (forall j₁₃: int, i₁₄: int ::
              (  j₁₃ <= j₁₃
                && i₁₄ <= i₁₄
                && 0 <= j₁₃
                && j₁₃ < j₂₈
                && 0 <= i₁₄
                && i₁₄ < i₂₉
                 ==> i₁₄ < 100000))
        && 0 <= x₃₀
        && x₃₀ <= j₂₈
        && (forall x₂₀: int ::
              (  x₂₀ <= x₂₀
                && 0 <= x₂₀
                && x₂₀ < x₃₀
                 ==> x₂₀ < j₂₈))
        && 0 <= x₃₁
        && x₃₁ <= j₂₈
        && (forall x₂₂: int ::
              (  x₂₂ <= x₂₂
                && 0 <= x₂₂
                && x₂₂ < x₃₁
                 ==> x₂₂ < j₂₈))
        && x₃₁ < j₂₈
         ==> x₃₀ < j₂₈
          || i₂₉ < 100000
          || i₂₆ < 100000
          || x₃₁ <= C₂₇[x₃₁]));

