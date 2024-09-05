data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₃₁: [int]int, i₃₂: int, ret₃₇: int, i₃₈: int, ret₄₃: int, i₄₄: int, x₄₆: [int]int, i₄₇: int, i₅₃: int ::
      (  0 <= i₃₂
        && i₃₂ <= 60
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₂
                 ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                        i₁₄ < 60
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₂
                        && x₃₁[x₁₅] == __VERIFIER_nondet_int₃₁₃)))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₂)
                || x₃₁[x₁₅] == x[x₁₅])
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₂
                 ==> i₁₄ < 60))
        && 0 <= i₃₈
        && i₃₈ <= 60
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> i₅ < 60))
        && 0 <= i₄₄
        && i₄₄ <= 60
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₄
                 ==> i₅ < 60))
        && 0 <= i₄₇
        && i₄₇ <= 59
        && (forall x₂₁: int, i₂₀: int ::
              (  x₂₁ == i₂₀
                && 0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> (exists i₂₀: int ::
                        i₂₀ < 59
                        && x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i₄₇
                        && x₄₆[x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][1 + i₂₀])))
        && (forall x₂₁: int ::
                (exists i₂₀: int ::
                        x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i₄₇)
                || x₄₆[x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][x₂₁])
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> i₂₀ < 59))
        && 0 <= i₅₃
        && i₅₃ <= 60
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₃
                 ==> i₅ < 60))
         ==> ret₃₇ == ret₄₃
          || i₅₃ < 60
          || i₄₇ < 60 - 1
          || i₄₄ < 60
          || i₃₈ < 60
          || i₃₂ < 60));

goal (forall x: [int]int, x₃₁: [int]int, i₃₂: int, ret₃₇: int, i₃₈: int, i₄₄: int, x₄₆: [int]int, i₄₇: int, ret₅₂: int, i₅₃: int ::
      (  0 <= i₃₂
        && i₃₂ <= 60
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₂
                 ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                        i₁₄ < 60
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₂
                        && x₃₁[x₁₅] == __VERIFIER_nondet_int₃₁₃)))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₂)
                || x₃₁[x₁₅] == x[x₁₅])
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₂
                 ==> i₁₄ < 60))
        && 0 <= i₃₈
        && i₃₈ <= 60
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> i₅ < 60))
        && 0 <= i₄₄
        && i₄₄ <= 60
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₄
                 ==> i₅ < 60))
        && 0 <= i₄₇
        && i₄₇ <= 59
        && (forall x₂₁: int, i₂₀: int ::
              (  x₂₁ == i₂₀
                && 0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> (exists i₂₀: int ::
                        i₂₀ < 59
                        && x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i₄₇
                        && x₄₆[x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][1 + i₂₀])))
        && (forall x₂₁: int ::
                (exists i₂₀: int ::
                        x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i₄₇)
                || x₄₆[x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][x₂₁])
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> i₂₀ < 59))
        && 0 <= i₅₃
        && i₅₃ <= 60
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₃
                 ==> i₅ < 60))
         ==> ret₃₇ == ret₅₂
          || i₅₃ < 60
          || i₄₇ < 60 - 1
          || i₄₄ < 60
          || i₃₈ < 60
          || i₃₂ < 60));

