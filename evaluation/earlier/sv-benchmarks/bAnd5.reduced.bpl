data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int ::
      1 <= N);

goal (forall N₃₅: int, x: [int]int, x₃₆: [int]int, i₃₇: int, res₄₁: int, i₄₂: int, res₄₇: int, i₄₈: int, x₅₀: [int]int, i₅₁: int, i₅₇: int ::
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
              (  0 <= i₁₄
                && i₁₄ < i₃₇
                 ==> i₁₄ < N₃₅))
        && 1 <= i₄₂
        && i₄₂ <= N₃₅
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₂
                 ==> i₄ < N₃₅))
        && 1 <= i₄₈
        && i₄₈ <= N₃₅
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₈
                 ==> i₄ < N₃₅))
        && 0 <= i₅₁
        && i₅₁ <= -1 + N₃₅
        && (forall x₂₅: int, i₂₄: int ::
              (  x₂₅ == i₂₄
                && 0 <= i₂₄
                && i₂₄ < i₅₁
                 ==> (exists i₂₄: int ::
                        i₂₄ < -1 + N₃₅
                        && x₂₅ == i₂₄
                        && 0 <= i₂₄
                        && i₂₄ < i₅₁
                        && x₅₀[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
        && (forall x₂₅: int ::
                (exists i₂₄: int ::
                        x₂₅ == i₂₄
                        && 0 <= i₂₄
                        && i₂₄ < i₅₁)
                || x₅₀[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅])
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₅₁
                 ==> i₂₄ < -1 + N₃₅))
        && 1 <= i₅₇
        && i₅₇ <= N₃₅
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₅₇
                 ==> i₄ < N₃₅))
         ==> res₄₁ == res₄₇
          || i₅₇ < N₃₅
          || i₅₁ < N₃₅ - 1
          || i₄₈ < N₃₅
          || i₄₂ < N₃₅
          || i₃₇ < N₃₅));

goal (forall N₃₅: int, x: [int]int, x₃₆: [int]int, i₃₇: int, res₄₁: int, i₄₂: int, i₄₈: int, x₅₀: [int]int, i₅₁: int, res₅₆: int, i₅₇: int ::
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
              (  0 <= i₁₄
                && i₁₄ < i₃₇
                 ==> i₁₄ < N₃₅))
        && 1 <= i₄₂
        && i₄₂ <= N₃₅
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₂
                 ==> i₄ < N₃₅))
        && 1 <= i₄₈
        && i₄₈ <= N₃₅
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₈
                 ==> i₄ < N₃₅))
        && 0 <= i₅₁
        && i₅₁ <= -1 + N₃₅
        && (forall x₂₅: int, i₂₄: int ::
              (  x₂₅ == i₂₄
                && 0 <= i₂₄
                && i₂₄ < i₅₁
                 ==> (exists i₂₄: int ::
                        i₂₄ < -1 + N₃₅
                        && x₂₅ == i₂₄
                        && 0 <= i₂₄
                        && i₂₄ < i₅₁
                        && x₅₀[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
        && (forall x₂₅: int ::
                (exists i₂₄: int ::
                        x₂₅ == i₂₄
                        && 0 <= i₂₄
                        && i₂₄ < i₅₁)
                || x₅₀[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅])
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₅₁
                 ==> i₂₄ < -1 + N₃₅))
        && 1 <= i₅₇
        && i₅₇ <= N₃₅
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₅₇
                 ==> i₄ < N₃₅))
         ==> res₄₁ == res₅₆
          || i₅₇ < N₃₅
          || i₅₁ < N₃₅ - 1
          || i₄₈ < N₃₅
          || i₄₂ < N₃₅
          || i₃₇ < N₃₅));

