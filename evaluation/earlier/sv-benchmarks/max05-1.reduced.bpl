data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₃₁: [int]int, i₃₂: int, ret₃₇: int, i₃₈: int, ret₄₃: int, i₄₄: int, x₄₆: [int]int, i₄₇: int, i₅₃: int ::
      (  0 <= i₃₂
        && i₃₂ <= 5
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₂
                 ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                        i₁₄ < 5
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
                 ==> i₁₄ < 5))
        && 0 <= i₃₈
        && i₃₈ <= 5
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> i₅ < 5))
        && 0 <= i₄₄
        && i₄₄ <= 5
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₄
                 ==> i₅ < 5))
        && 0 <= i₄₇
        && i₄₇ <= 4
        && (forall x₂₁: int, i₂₀: int ::
              (  x₂₁ == i₂₀
                && 0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> (exists i₂₀: int ::
                        i₂₀ < 4
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
                 ==> i₂₀ < 4))
        && 0 <= i₅₃
        && i₅₃ <= 5
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₃
                 ==> i₅ < 5))
         ==> ret₃₇ == ret₄₃
          || i₅₃ < 5
          || i₄₇ < 5 - 1
          || i₄₄ < 5
          || i₃₈ < 5
          || i₃₂ < 5));

goal (forall x: [int]int, x₃₁: [int]int, i₃₂: int, ret₃₇: int, i₃₈: int, i₄₄: int, x₄₆: [int]int, i₄₇: int, ret₅₂: int, i₅₃: int ::
      (  0 <= i₃₂
        && i₃₂ <= 5
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₂
                 ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                        i₁₄ < 5
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
                 ==> i₁₄ < 5))
        && 0 <= i₃₈
        && i₃₈ <= 5
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> i₅ < 5))
        && 0 <= i₄₄
        && i₄₄ <= 5
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₄
                 ==> i₅ < 5))
        && 0 <= i₄₇
        && i₄₇ <= 4
        && (forall x₂₁: int, i₂₀: int ::
              (  x₂₁ == i₂₀
                && 0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> (exists i₂₀: int ::
                        i₂₀ < 4
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
                 ==> i₂₀ < 4))
        && 0 <= i₅₃
        && i₅₃ <= 5
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₃
                 ==> i₅ < 5))
         ==> ret₃₇ == ret₅₂
          || i₅₃ < 5
          || i₄₇ < 5 - 1
          || i₄₄ < 5
          || i₃₈ < 5
          || i₃₂ < 5));

