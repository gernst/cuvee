data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall x: [int]int, x₂₆: [int]int, i₂₇: int, ret₃₂: int, i₃₃: int, ret₃₈: int, i₃₉: int, x₄₁: [int]int, i₄₂: int, i₄₈: int ::
      (  0 <= i₂₇
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₇
                 ==> (exists nondet_int₄₁₀: int ::
                        -2147483648 <= nondet_int₄₁₀
                        && nondet_int₄₁₀ < 2147483648
                        && i₁₁ < 40
                        && x₂₆[i₁₁] == nondet_int₄₁₀)))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₇
                || x₂₆[i₁₁] == x[i₁₁])
        && 0 <= i₃₃
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₃
                 ==> x₂₆[i₂] % 2 == 0
                    && i₂ < 40
                  ||   (x₂₆[i₂] % 2 == 0
                       ==> false)
                    && i₂ < 40))
        && 0 <= i₃₉
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₉
                 ==> x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₂] % 2 == 0
                    && i₂ < 40
                  ||   (x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < 40))
        && 0 <= i₄₂
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₄₂
                 ==> i₁₆ < 39
                  && x₄₁[i₁₆] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₆]))
        && (forall i₁₆: int ::
                  0 <= i₁₆
                  && i₁₆ < i₄₂
                || x₄₁[i₁₆] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₆])
        && 0 <= i₄₈
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₈
                 ==> x₄₁[40 - 1 := x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][0]][i₂] % 2 == 0
                    && i₂ < 40
                  ||   (x₄₁[40 - 1 := x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < 40))
         ==> ret₃₂ == ret₃₈
          || i₄₈ < 40
          || i₄₂ < 40 - 1
          || i₃₉ < 40
          || i₃₃ < 40
          || i₂₇ < 40));

goal {:named "assert"} (forall x: [int]int, x₂₆: [int]int, i₂₇: int, ret₃₂: int, i₃₃: int, i₃₉: int, x₄₁: [int]int, i₄₂: int, ret₄₇: int, i₄₈: int ::
      (  0 <= i₂₇
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₇
                 ==> (exists nondet_int₄₁₀: int ::
                        -2147483648 <= nondet_int₄₁₀
                        && nondet_int₄₁₀ < 2147483648
                        && i₁₁ < 40
                        && x₂₆[i₁₁] == nondet_int₄₁₀)))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₇
                || x₂₆[i₁₁] == x[i₁₁])
        && 0 <= i₃₃
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₃
                 ==> x₂₆[i₂] % 2 == 0
                    && i₂ < 40
                  ||   (x₂₆[i₂] % 2 == 0
                       ==> false)
                    && i₂ < 40))
        && 0 <= i₃₉
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₉
                 ==> x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₂] % 2 == 0
                    && i₂ < 40
                  ||   (x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < 40))
        && 0 <= i₄₂
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₄₂
                 ==> i₁₆ < 39
                  && x₄₁[i₁₆] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₆]))
        && (forall i₁₆: int ::
                  0 <= i₁₆
                  && i₁₆ < i₄₂
                || x₄₁[i₁₆] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₆])
        && 0 <= i₄₈
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₈
                 ==> x₄₁[40 - 1 := x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][0]][i₂] % 2 == 0
                    && i₂ < 40
                  ||   (x₄₁[40 - 1 := x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < 40))
         ==> ret₃₂ == ret₄₇
          || i₄₈ < 40
          || i₄₂ < 40 - 1
          || i₃₉ < 40
          || i₃₃ < 40
          || i₂₇ < 40));

