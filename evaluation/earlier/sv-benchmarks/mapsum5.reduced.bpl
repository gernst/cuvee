data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int ::
      0 <= N);

goal (forall N₃₅: int, x: [int]int, x₃₆: [int]int, i₃₇: int, ret₄₂: int, i₄₃: int, ret₄₈: int, i₄₉: int, x₅₁: [int]int, i₅₂: int, i₅₈: int ::
      (  1 < N₃₅
        && 0 <= i₃₇
        && i₃₇ <= N₃₅
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₇
                 ==> (exists __VERIFIER_nondet_int₂₁₃: int, i₁₄: int ::
                        i₁₄ < N₃₅
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₇
                        && x₃₆[x₁₅] == __VERIFIER_nondet_int₂₁₃)))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₇)
                || x₃₆[x₁₅] == x[x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₇
                 ==> i₁₄ < N₃₅))
        && 0 <= i₄₃
        && i₄₃ <= N₃₅
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₄₃
                 ==> i₄ < N₃₅))
        && 0 <= i₄₉
        && i₄₉ <= N₃₅
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₄₉
                 ==> i₄ < N₃₅))
        && 0 <= i₅₂
        && i₅₂ <= -1 + N₃₅
        && (forall x₂₅: int, i₂₄: int ::
              (  x₂₅ == i₂₄
                && 0 <= i₂₄
                && i₂₄ < i₅₂
                 ==> (exists i₂₄: int ::
                        i₂₄ < -1 + N₃₅
                        && x₂₅ == i₂₄
                        && 0 <= i₂₄
                        && i₂₄ < i₅₂
                        && x₅₁[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
        && (forall x₂₅: int ::
                (exists i₂₄: int ::
                        x₂₅ == i₂₄
                        && 0 <= i₂₄
                        && i₂₄ < i₅₂)
                || x₅₁[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅])
        && (forall i₂₄: int ::
              (  i₂₄ <= i₂₄
                && 0 <= i₂₄
                && i₂₄ < i₅₂
                 ==> i₂₄ < -1 + N₃₅))
        && 0 <= i₅₈
        && i₅₈ <= N₃₅
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₅₈
                 ==> i₄ < N₃₅))
         ==> ret₄₂ == ret₄₈
          || i₅₈ < N₃₅
          || i₅₂ < N₃₅ - 1
          || i₄₉ < N₃₅
          || i₄₃ < N₃₅
          || i₃₇ < N₃₅));

goal (forall N₃₅: int, x: [int]int, x₃₆: [int]int, i₃₇: int, ret₄₂: int, i₄₃: int, i₄₉: int, x₅₁: [int]int, i₅₂: int, ret₅₇: int, i₅₈: int ::
      (  1 < N₃₅
        && 0 <= i₃₇
        && i₃₇ <= N₃₅
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₇
                 ==> (exists __VERIFIER_nondet_int₂₁₃: int, i₁₄: int ::
                        i₁₄ < N₃₅
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₇
                        && x₃₆[x₁₅] == __VERIFIER_nondet_int₂₁₃)))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₇)
                || x₃₆[x₁₅] == x[x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₇
                 ==> i₁₄ < N₃₅))
        && 0 <= i₄₃
        && i₄₃ <= N₃₅
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₄₃
                 ==> i₄ < N₃₅))
        && 0 <= i₄₉
        && i₄₉ <= N₃₅
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₄₉
                 ==> i₄ < N₃₅))
        && 0 <= i₅₂
        && i₅₂ <= -1 + N₃₅
        && (forall x₂₅: int, i₂₄: int ::
              (  x₂₅ == i₂₄
                && 0 <= i₂₄
                && i₂₄ < i₅₂
                 ==> (exists i₂₄: int ::
                        i₂₄ < -1 + N₃₅
                        && x₂₅ == i₂₄
                        && 0 <= i₂₄
                        && i₂₄ < i₅₂
                        && x₅₁[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
        && (forall x₂₅: int ::
                (exists i₂₄: int ::
                        x₂₅ == i₂₄
                        && 0 <= i₂₄
                        && i₂₄ < i₅₂)
                || x₅₁[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅])
        && (forall i₂₄: int ::
              (  i₂₄ <= i₂₄
                && 0 <= i₂₄
                && i₂₄ < i₅₂
                 ==> i₂₄ < -1 + N₃₅))
        && 0 <= i₅₈
        && i₅₈ <= N₃₅
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₅₈
                 ==> i₄ < N₃₅))
         ==> ret₄₂ == ret₅₇
          || i₅₈ < N₃₅
          || i₅₂ < N₃₅ - 1
          || i₄₉ < N₃₅
          || i₄₃ < N₃₅
          || i₃₇ < N₃₅));

