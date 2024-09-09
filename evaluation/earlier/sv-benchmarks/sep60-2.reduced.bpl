data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₆: [int]int, i₂₇: int, ret₃₂: int, i₃₃: int, ret₃₈: int, i₃₉: int, x₄₁: [int]int, i₄₂: int, i₄₈: int ::
      (  0 <= i₂₇
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int ::
                        i₁₁ < 60
                        && x₂₆[i₁₁] == __VERIFIER_nondet_int₄₁₀)))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₇
                || x₂₆[i₁₁] == x[i₁₁])
        && 0 <= i₃₃
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₃
                 ==> x₂₆[i₂] % 2 == 0
                    && i₂ < 60
                  ||   (x₂₆[i₂] % 2 == 0
                       ==> false)
                    && i₂ < 60))
        && 0 <= i₃₉
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₉
                 ==> x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₂] % 2 == 0
                    && i₂ < 60
                  ||   (x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < 60))
        && 0 <= i₄₂
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₄₂
                 ==> i₁₆ < 59
                  && x₄₁[i₁₆] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₆]))
        && (forall i₁₆: int ::
                  0 <= i₁₆
                  && i₁₆ < i₄₂
                || x₄₁[i₁₆] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₆])
        && 0 <= i₄₈
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₈
                 ==> x₄₁[60 - 1 := x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][0]][i₂] % 2 == 0
                    && i₂ < 60
                  ||   (x₄₁[60 - 1 := x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < 60))
         ==> ret₃₂ == ret₃₈
          || i₄₈ < 60
          || i₄₂ < 60 - 1
          || i₃₉ < 60
          || i₃₃ < 60
          || i₂₇ < 60));

goal (forall x: [int]int, x₂₆: [int]int, i₂₇: int, ret₃₂: int, i₃₃: int, i₃₉: int, x₄₁: [int]int, i₄₂: int, ret₄₇: int, i₄₈: int ::
      (  0 <= i₂₇
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int ::
                        i₁₁ < 60
                        && x₂₆[i₁₁] == __VERIFIER_nondet_int₄₁₀)))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₇
                || x₂₆[i₁₁] == x[i₁₁])
        && 0 <= i₃₃
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₃
                 ==> x₂₆[i₂] % 2 == 0
                    && i₂ < 60
                  ||   (x₂₆[i₂] % 2 == 0
                       ==> false)
                    && i₂ < 60))
        && 0 <= i₃₉
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₉
                 ==> x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₂] % 2 == 0
                    && i₂ < 60
                  ||   (x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < 60))
        && 0 <= i₄₂
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₄₂
                 ==> i₁₆ < 59
                  && x₄₁[i₁₆] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₆]))
        && (forall i₁₆: int ::
                  0 <= i₁₆
                  && i₁₆ < i₄₂
                || x₄₁[i₁₆] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₆])
        && 0 <= i₄₈
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₈
                 ==> x₄₁[60 - 1 := x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][0]][i₂] % 2 == 0
                    && i₂ < 60
                  ||   (x₄₁[60 - 1 := x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][0]][i₂] % 2 == 0
                       ==> false)
                    && i₂ < 60))
         ==> ret₃₂ == ret₄₇
          || i₄₈ < 60
          || i₄₂ < 60 - 1
          || i₃₉ < 60
          || i₃₃ < 60
          || i₂₇ < 60));

