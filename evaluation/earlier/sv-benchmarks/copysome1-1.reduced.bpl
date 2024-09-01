data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a1₂₀: [int]int, a2₂₁: [int]int, i₂₂: int, a2₂₃: [int]int, i₂₄: int, x₂₅: int ::
      (  0 <= i₂₂
        && i₂₂ <= 200000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        i₇ < 200000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₂
                        && a1₂₀[x₈] == __VERIFIER_nondet_int₁₅)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₂)
                || a1₂₀[x₈] == a1[x₈])
        && (forall x₉: int, i₇: int ::
              (  x₉ == i₇
                && 0 <= i₇
                && i₇ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 200000
                        && x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₂
                        && a2₂₁[x₉] == __VERIFIER_nondet_int₂₆)))
        && (forall x₉: int ::
                (exists i₇: int ::
                        x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₂)
                || a2₂₁[x₉] == a2[x₉])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₂₂
                 ==> i₇ < 200000))
        && 0 <= i₂₄
        && i₂₄ <= 200000
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₄
                 ==> (exists i₁₃: int ::
                      (i₁₃ == 150000
                         ==> false))))
        && (forall x₁₄: int ::
                (exists i₁₃: int ::
                        x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₄)
                || a2₂₃[x₁₄] == a2₂₁[x₁₄])
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₄
                 ==> i₁₃ < 200000))
        && 0 <= x₂₅
        && x₂₅ <= 200000
        && (forall x₁₈: int ::
              (  x₁₈ <= x₁₈
                && 0 <= x₁₈
                && x₁₈ < x₂₅
                 ==> x₁₈ < 200000))
        && x₂₅ < 200000
         ==> x₂₅ == 150000
          || i₂₄ < 200000
          || i₂₂ < 200000
          || a1₂₀[x₂₅] == a2₂₃[x₂₅]));

