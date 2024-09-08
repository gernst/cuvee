data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₆: [int]int, i₂₇: int, res₃₁: int, i₃₂: int, res₃₇: int, i₃₈: int, x₄₀: [int]int, i₄₁: int, i₄₇: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int ::
                        i₁₃ < 100
                        && x₂₆[i₁₃] == __VERIFIER_nondet_int₂₁₂)))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₂₇
                || x₂₆[i₁₃] == x[i₁₃])
        && 1 <= i₃₂
        && i₃₂ <= 100
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₂
                 ==> i₄ < 100))
        && 1 <= i₃₈
        && i₃₈ <= 100
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₈
                 ==> i₄ < 100))
        && 0 <= i₄₁
        && i₄₁ <= 99
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₁
                 ==> i₁₈ < 99
                  && x₄₀[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₈]))
        && (forall i₁₈: int ::
                  0 <= i₁₈
                  && i₁₈ < i₄₁
                || x₄₀[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₈])
        && 1 <= i₄₇
        && i₄₇ <= 100
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₇
                 ==> i₄ < 100))
         ==> res₃₁ == res₃₇
          || i₄₇ < 100
          || i₄₁ < 100 - 1
          || i₃₈ < 100
          || i₃₂ < 100
          || i₂₇ < 100));

goal (forall x: [int]int, x₂₆: [int]int, i₂₇: int, res₃₁: int, i₃₂: int, i₃₈: int, x₄₀: [int]int, i₄₁: int, res₄₆: int, i₄₇: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int ::
                        i₁₃ < 100
                        && x₂₆[i₁₃] == __VERIFIER_nondet_int₂₁₂)))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₂₇
                || x₂₆[i₁₃] == x[i₁₃])
        && 1 <= i₃₂
        && i₃₂ <= 100
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₂
                 ==> i₄ < 100))
        && 1 <= i₃₈
        && i₃₈ <= 100
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₈
                 ==> i₄ < 100))
        && 0 <= i₄₁
        && i₄₁ <= 99
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₁
                 ==> i₁₈ < 99
                  && x₄₀[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₈]))
        && (forall i₁₈: int ::
                  0 <= i₁₈
                  && i₁₈ < i₄₁
                || x₄₀[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₈])
        && 1 <= i₄₇
        && i₄₇ <= 100
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₇
                 ==> i₄ < 100))
         ==> res₃₁ == res₄₆
          || i₄₇ < 100
          || i₄₁ < 100 - 1
          || i₃₈ < 100
          || i₃₂ < 100
          || i₂₇ < 100));

