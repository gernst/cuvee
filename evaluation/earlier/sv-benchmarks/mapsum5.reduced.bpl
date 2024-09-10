data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall N₃₃: int, x: [int]int, x₃₄: [int]int, i₃₅: int, ret₄₀: int, i₄₁: int, ret₄₆: int, i₄₇: int, x₄₉: [int]int, i₅₀: int, i₅₆: int ::
      (  1 < N₃₃
        && 0 <= i₃₅
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₅
                 ==> (exists nondet_int₂₁₃: int ::
                        i₁₄ < N₃₃
                        && x₃₄[i₁₄] == nondet_int₂₁₃)))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₃₅
                || x₃₄[i₁₄] == x[i₁₄])
        && 0 <= i₄₁
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < N₃₃))
        && 0 <= i₄₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₇
                 ==> i₄ < N₃₃))
        && 0 <= i₅₀
        && (forall i₂₃: int ::
              (  0 <= i₂₃
                && i₂₃ < i₅₀
                 ==> i₂₃ < -1 + N₃₃
                  && x₄₉[i₂₃] == x₃₄[0 := x₃₄[1]][1 := x₃₄[0]][1 + i₂₃]))
        && (forall i₂₃: int ::
                  0 <= i₂₃
                  && i₂₃ < i₅₀
                || x₄₉[i₂₃] == x₃₄[0 := x₃₄[1]][1 := x₃₄[0]][i₂₃])
        && 0 <= i₅₆
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₅₆
                 ==> i₄ < N₃₃))
         ==> ret₄₀ == ret₄₆
          || i₅₆ < N₃₃
          || i₅₀ < N₃₃ - 1
          || i₄₇ < N₃₃
          || i₄₁ < N₃₃
          || i₃₅ < N₃₃));

goal {:named "assert"} (forall N₃₃: int, x: [int]int, x₃₄: [int]int, i₃₅: int, ret₄₀: int, i₄₁: int, i₄₇: int, x₄₉: [int]int, i₅₀: int, ret₅₅: int, i₅₆: int ::
      (  1 < N₃₃
        && 0 <= i₃₅
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₅
                 ==> (exists nondet_int₂₁₃: int ::
                        i₁₄ < N₃₃
                        && x₃₄[i₁₄] == nondet_int₂₁₃)))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₃₅
                || x₃₄[i₁₄] == x[i₁₄])
        && 0 <= i₄₁
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < N₃₃))
        && 0 <= i₄₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₇
                 ==> i₄ < N₃₃))
        && 0 <= i₅₀
        && (forall i₂₃: int ::
              (  0 <= i₂₃
                && i₂₃ < i₅₀
                 ==> i₂₃ < -1 + N₃₃
                  && x₄₉[i₂₃] == x₃₄[0 := x₃₄[1]][1 := x₃₄[0]][1 + i₂₃]))
        && (forall i₂₃: int ::
                  0 <= i₂₃
                  && i₂₃ < i₅₀
                || x₄₉[i₂₃] == x₃₄[0 := x₃₄[1]][1 := x₃₄[0]][i₂₃])
        && 0 <= i₅₆
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₅₆
                 ==> i₄ < N₃₃))
         ==> ret₄₀ == ret₅₅
          || i₅₆ < N₃₃
          || i₅₀ < N₃₃ - 1
          || i₄₇ < N₃₃
          || i₄₁ < N₃₃
          || i₃₅ < N₃₃));

