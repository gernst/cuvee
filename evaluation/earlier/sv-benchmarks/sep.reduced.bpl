data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₉: int, x: [int]int, ret₃₃: int, i₃₄: int, ret₃₉: int, i₄₀: int, x₄₂: [int]int, i₄₃: int, i₄₉: int ::
      (  1 < N₂₉
        && 0 <= i₃₄
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₄
                 ==> x[i₂] % 2 == 0
                    && i₂ < N₂₉
                  ||   (x[i₂] % 2 == 0
                       ==> false)
                    && i₂ < N₂₉))
        && 0 <= i₄₀
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₀
                 ==> x[0 := x[1]][1 := x[0]][i₂] % 2 == 0
                    && i₂ < N₂₉
                  ||   (x[0 := x[1]][1 := x[0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < N₂₉))
        && 0 <= i₄₃
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₄₃
                 ==> i₁₇ < -1 + N₂₉
                  && x₄₂[i₁₇] == x[0 := x[1]][1 := x[0]][1 + i₁₇]))
        && (forall i₁₇: int ::
                  0 <= i₁₇
                  && i₁₇ < i₄₃
                || x₄₂[i₁₇] == x[0 := x[1]][1 := x[0]][i₁₇])
        && 0 <= i₄₉
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₉
                 ==> x₄₂[N₂₉ - 1 := x[0 := x[1]][1 := x[0]][0]][i₂] % 2 == 0
                    && i₂ < N₂₉
                  ||   (x₄₂[N₂₉ - 1 := x[0 := x[1]][1 := x[0]][0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < N₂₉))
         ==> ret₃₃ == ret₃₉
          || i₄₉ < N₂₉
          || i₄₃ < N₂₉ - 1
          || i₄₀ < N₂₉
          || i₃₄ < N₂₉));

goal (forall N₂₉: int, x: [int]int, ret₃₃: int, i₃₄: int, i₄₀: int, x₄₂: [int]int, i₄₃: int, ret₄₈: int, i₄₉: int ::
      (  1 < N₂₉
        && 0 <= i₃₄
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₄
                 ==> x[i₂] % 2 == 0
                    && i₂ < N₂₉
                  ||   (x[i₂] % 2 == 0
                       ==> false)
                    && i₂ < N₂₉))
        && 0 <= i₄₀
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₀
                 ==> x[0 := x[1]][1 := x[0]][i₂] % 2 == 0
                    && i₂ < N₂₉
                  ||   (x[0 := x[1]][1 := x[0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < N₂₉))
        && 0 <= i₄₃
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₄₃
                 ==> i₁₇ < -1 + N₂₉
                  && x₄₂[i₁₇] == x[0 := x[1]][1 := x[0]][1 + i₁₇]))
        && (forall i₁₇: int ::
                  0 <= i₁₇
                  && i₁₇ < i₄₃
                || x₄₂[i₁₇] == x[0 := x[1]][1 := x[0]][i₁₇])
        && 0 <= i₄₉
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₉
                 ==> x₄₂[N₂₉ - 1 := x[0 := x[1]][1 := x[0]][0]][i₂] % 2 == 0
                    && i₂ < N₂₉
                  ||   (x₄₂[N₂₉ - 1 := x[0 := x[1]][1 := x[0]][0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < N₂₉))
         ==> ret₃₃ == ret₄₈
          || i₄₉ < N₂₉
          || i₄₃ < N₂₉ - 1
          || i₄₀ < N₂₉
          || i₃₄ < N₂₉));

