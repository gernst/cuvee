data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall x: [int]int, x₂₆: [int]int, i₂₇: int, ret₃₂: int, i₃₃: int, ret₃₈: int, i₃₉: int, x₄₁: [int]int, i₄₂: int, i₄₈: int ::
      (  0 <= i₂₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists nondet_int₂₁₂: int ::
                        i₁₃ < 5
                        && x₂₆[i₁₃] == nondet_int₂₁₂)))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₂₇
                || x₂₆[i₁₃] == x[i₁₃])
        && 0 <= i₃₃
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₃
                 ==> i₄ < 5))
        && 0 <= i₃₉
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₉
                 ==> i₄ < 5))
        && 0 <= i₄₂
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₂
                 ==> i₁₈ < 4
                  && x₄₁[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₈]))
        && (forall i₁₈: int ::
                  0 <= i₁₈
                  && i₁₈ < i₄₂
                || x₄₁[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₈])
        && 0 <= i₄₈
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₈
                 ==> i₄ < 5))
         ==> ret₃₂ == ret₃₈
          || i₄₈ < 5
          || i₄₂ < 5 - 1
          || i₃₉ < 5
          || i₃₃ < 5
          || i₂₇ < 5));

goal {:named "assert"} (forall x: [int]int, x₂₆: [int]int, i₂₇: int, ret₃₂: int, i₃₃: int, i₃₉: int, x₄₁: [int]int, i₄₂: int, ret₄₇: int, i₄₈: int ::
      (  0 <= i₂₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists nondet_int₂₁₂: int ::
                        i₁₃ < 5
                        && x₂₆[i₁₃] == nondet_int₂₁₂)))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₂₇
                || x₂₆[i₁₃] == x[i₁₃])
        && 0 <= i₃₃
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₃
                 ==> i₄ < 5))
        && 0 <= i₃₉
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₉
                 ==> i₄ < 5))
        && 0 <= i₄₂
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₂
                 ==> i₁₈ < 4
                  && x₄₁[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₈]))
        && (forall i₁₈: int ::
                  0 <= i₁₈
                  && i₁₈ < i₄₂
                || x₄₁[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₈])
        && 0 <= i₄₈
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₈
                 ==> i₄ < 5))
         ==> ret₃₂ == ret₄₇
          || i₄₈ < 5
          || i₄₂ < 5 - 1
          || i₃₉ < 5
          || i₃₃ < 5
          || i₂₇ < 5));

