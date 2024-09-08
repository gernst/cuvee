data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₆: [int]int, i₂₇: int, ret₃₂: int, i₃₃: int, ret₃₈: int, i₃₉: int, x₄₁: [int]int, i₄₂: int, i₄₈: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100000
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int ::
                        i₁₃ < 100000
                        && x₂₆[i₁₃] == __VERIFIER_nondet_int₂₁₂)))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₂₇
                || x₂₆[i₁₃] == x[i₁₃])
        && 0 <= i₃₃
        && i₃₃ <= 100000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₃
                 ==> i₄ < 100000))
        && 0 <= i₃₉
        && i₃₉ <= 100000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₉
                 ==> i₄ < 100000))
        && 0 <= i₄₂
        && i₄₂ <= 99999
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₂
                 ==> i₁₈ < 99999
                  && x₄₁[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₈]))
        && (forall i₁₈: int ::
                  0 <= i₁₈
                  && i₁₈ < i₄₂
                || x₄₁[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₈])
        && 0 <= i₄₈
        && i₄₈ <= 100000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₈
                 ==> i₄ < 100000))
         ==> ret₃₂ == ret₃₈
          || i₄₈ < 100000
          || i₄₂ < 100000 - 1
          || i₃₉ < 100000
          || i₃₃ < 100000
          || i₂₇ < 100000));

goal (forall x: [int]int, x₂₆: [int]int, i₂₇: int, ret₃₂: int, i₃₃: int, i₃₉: int, x₄₁: [int]int, i₄₂: int, ret₄₇: int, i₄₈: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100000
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int ::
                        i₁₃ < 100000
                        && x₂₆[i₁₃] == __VERIFIER_nondet_int₂₁₂)))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₂₇
                || x₂₆[i₁₃] == x[i₁₃])
        && 0 <= i₃₃
        && i₃₃ <= 100000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₃
                 ==> i₄ < 100000))
        && 0 <= i₃₉
        && i₃₉ <= 100000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₉
                 ==> i₄ < 100000))
        && 0 <= i₄₂
        && i₄₂ <= 99999
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₂
                 ==> i₁₈ < 99999
                  && x₄₁[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][1 + i₁₈]))
        && (forall i₁₈: int ::
                  0 <= i₁₈
                  && i₁₈ < i₄₂
                || x₄₁[i₁₈] == x₂₆[0 := x₂₆[1]][1 := x₂₆[0]][i₁₈])
        && 0 <= i₄₈
        && i₄₈ <= 100000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₈
                 ==> i₄ < 100000))
         ==> ret₃₂ == ret₄₇
          || i₄₈ < 100000
          || i₄₂ < 100000 - 1
          || i₃₉ < 100000
          || i₃₃ < 100000
          || i₂₇ < 100000));

