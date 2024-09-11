data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall N₃₂: int, x: [int]int, ret₃₆: int, i₃₇: int, ret₄₂: int, i₄₃: int, x₄₅: [int]int, i₄₆: int, i₅₂: int ::
      (  1 < N₃₂
        && 0 <= i₃₇
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₇
                 ==> ret₄ < x[i₅]
                    && i₅ < N₃₂
                  ||   (ret₄ < x[i₅]
                       ==> false)
                    && i₅ < N₃₂))
        && 0 <= i₄₃
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₃
                 ==> ret₄ < x[0 := x[1]][1 := x[0]][i₅]
                    && i₅ < N₃₂
                  ||   (ret₄ < x[0 := x[1]][1 := x[0]][i₅]
                       ==> false)
                    && i₅ < N₃₂))
        && 0 <= i₄₆
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₄₆
                 ==> i₂₀ < -1 + N₃₂
                  && x₄₅[i₂₀] == x[0 := x[1]][1 := x[0]][1 + i₂₀]))
        && (forall i₂₀: int ::
                  0 <= i₂₀
                  && i₂₀ < i₄₆
                || x₄₅[i₂₀] == x[0 := x[1]][1 := x[0]][i₂₀])
        && 0 <= i₅₂
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₂
                 ==> ret₄ < x₄₅[N₃₂ - 1 := x[0 := x[1]][1 := x[0]][0]][i₅]
                    && i₅ < N₃₂
                  ||   (ret₄ < x₄₅[N₃₂ - 1 := x[0 := x[1]][1 := x[0]][0]][i₅]
                       ==> false)
                    && i₅ < N₃₂))
         ==> ret₃₆ == ret₄₂
          || i₅₂ < N₃₂
          || i₄₆ < N₃₂ - 1
          || i₄₃ < N₃₂
          || i₃₇ < N₃₂));

goal {:named "assert"} (forall N₃₂: int, x: [int]int, ret₃₆: int, i₃₇: int, i₄₃: int, x₄₅: [int]int, i₄₆: int, ret₅₁: int, i₅₂: int ::
      (  1 < N₃₂
        && 0 <= i₃₇
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₇
                 ==> ret₄ < x[i₅]
                    && i₅ < N₃₂
                  ||   (ret₄ < x[i₅]
                       ==> false)
                    && i₅ < N₃₂))
        && 0 <= i₄₃
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₃
                 ==> ret₄ < x[0 := x[1]][1 := x[0]][i₅]
                    && i₅ < N₃₂
                  ||   (ret₄ < x[0 := x[1]][1 := x[0]][i₅]
                       ==> false)
                    && i₅ < N₃₂))
        && 0 <= i₄₆
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₄₆
                 ==> i₂₀ < -1 + N₃₂
                  && x₄₅[i₂₀] == x[0 := x[1]][1 := x[0]][1 + i₂₀]))
        && (forall i₂₀: int ::
                  0 <= i₂₀
                  && i₂₀ < i₄₆
                || x₄₅[i₂₀] == x[0 := x[1]][1 := x[0]][i₂₀])
        && 0 <= i₅₂
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₂
                 ==> ret₄ < x₄₅[N₃₂ - 1 := x[0 := x[1]][1 := x[0]][0]][i₅]
                    && i₅ < N₃₂
                  ||   (ret₄ < x₄₅[N₃₂ - 1 := x[0 := x[1]][1 := x[0]][0]][i₅]
                       ==> false)
                    && i₅ < N₃₂))
         ==> ret₃₆ == ret₅₁
          || i₅₂ < N₃₂
          || i₄₆ < N₃₂ - 1
          || i₄₃ < N₃₂
          || i₃₇ < N₃₂));

