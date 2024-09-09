data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₆: [int]int, i₂₇: int, res₃₁: int, i₃₂: int, res₃₇: int, i₃₈: int, x₄₀: [int]int, i₄₁: int, i₄₇: int ::
      (  0 <= i₂₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int ::
                        i₁₃ < 10000
                        && x₂₆[i₁₃] == __VERIFIER_nondet_int₂₁₂)))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₂₇
                || x₂₆[i₁₃] == x[i₁₃])
        && 1 <= i₃₂
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₂
                 ==> i₄ < 10000))
        && 1 <= i₃₈
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₈
                 ==> i₄ < 10000))
        && 0 <= i₄₁
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₁
                 ==> i₁₈ < 9999
                  && x₄₀[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₈]))
        && (forall i₁₈: int ::
                  0 <= i₁₈
                  && i₁₈ < i₄₁
                || x₄₀[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₈])
        && 1 <= i₄₇
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₇
                 ==> i₄ < 10000))
         ==> res₃₁ == res₃₇
          || i₄₇ < 10000
          || i₄₁ < 10000 - 1
          || i₃₈ < 10000
          || i₃₂ < 10000
          || i₂₇ < 10000));

goal (forall x: [int]int, x₂₆: [int]int, i₂₇: int, res₃₁: int, i₃₂: int, i₃₈: int, x₄₀: [int]int, i₄₁: int, res₄₆: int, i₄₇: int ::
      (  0 <= i₂₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int ::
                        i₁₃ < 10000
                        && x₂₆[i₁₃] == __VERIFIER_nondet_int₂₁₂)))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₂₇
                || x₂₆[i₁₃] == x[i₁₃])
        && 1 <= i₃₂
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₂
                 ==> i₄ < 10000))
        && 1 <= i₃₈
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₈
                 ==> i₄ < 10000))
        && 0 <= i₄₁
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₁
                 ==> i₁₈ < 9999
                  && x₄₀[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₈]))
        && (forall i₁₈: int ::
                  0 <= i₁₈
                  && i₁₈ < i₄₁
                || x₄₀[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₈])
        && 1 <= i₄₇
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₇
                 ==> i₄ < 10000))
         ==> res₃₁ == res₄₆
          || i₄₇ < 10000
          || i₄₁ < 10000 - 1
          || i₃₈ < 10000
          || i₃₂ < 10000
          || i₂₇ < 10000));

