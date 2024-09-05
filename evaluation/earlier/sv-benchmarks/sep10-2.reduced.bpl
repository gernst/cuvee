data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, ret₄₀: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 10
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                        i₁₁ < 10
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₂₉
                        && x₂₈[x₁₂] == __VERIFIER_nondet_int₄₁₀)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₂₉)
                || x₂₈[x₁₂] == x[x₁₂])
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₉
                 ==> i₁₁ < 10))
        && 0 <= i₃₅
        && i₃₅ <= 10
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₅
                 ==> i₂ < 10))
        && 0 <= i₄₁
        && i₄₁ <= 10
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₁
                 ==> i₂ < 10))
        && 0 <= i₄₄
        && i₄₄ <= 9
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> (exists i₁₇: int ::
                        i₁₇ < 9
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₄₄
                        && x₄₃[x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₄₄)
                || x₄₃[x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₁₈])
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> i₁₇ < 9))
        && 0 <= i₅₀
        && i₅₀ <= 10
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₅₀
                 ==> i₂ < 10))
         ==> ret₃₄ == ret₄₀
          || i₅₀ < 10
          || i₄₄ < 10 - 1
          || i₄₁ < 10
          || i₃₅ < 10
          || i₂₉ < 10));

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, ret₄₉: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 10
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                        i₁₁ < 10
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₂₉
                        && x₂₈[x₁₂] == __VERIFIER_nondet_int₄₁₀)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₂₉)
                || x₂₈[x₁₂] == x[x₁₂])
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₉
                 ==> i₁₁ < 10))
        && 0 <= i₃₅
        && i₃₅ <= 10
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₅
                 ==> i₂ < 10))
        && 0 <= i₄₁
        && i₄₁ <= 10
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₁
                 ==> i₂ < 10))
        && 0 <= i₄₄
        && i₄₄ <= 9
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> (exists i₁₇: int ::
                        i₁₇ < 9
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₄₄
                        && x₄₃[x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₄₄)
                || x₄₃[x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₁₈])
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> i₁₇ < 9))
        && 0 <= i₅₀
        && i₅₀ <= 10
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₅₀
                 ==> i₂ < 10))
         ==> ret₃₄ == ret₄₉
          || i₅₀ < 10
          || i₄₄ < 10 - 1
          || i₄₁ < 10
          || i₃₅ < 10
          || i₂₉ < 10));

