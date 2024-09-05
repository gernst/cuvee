data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, ret₄₀: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 5
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                        i₁₁ < 5
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
                 ==> i₁₁ < 5))
        && 0 <= i₃₅
        && i₃₅ <= 5
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₅
                 ==> i₂ < 5))
        && 0 <= i₄₁
        && i₄₁ <= 5
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₁
                 ==> i₂ < 5))
        && 0 <= i₄₄
        && i₄₄ <= 4
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> (exists i₁₇: int ::
                        i₁₇ < 4
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
                 ==> i₁₇ < 4))
        && 0 <= i₅₀
        && i₅₀ <= 5
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₅₀
                 ==> i₂ < 5))
         ==> ret₃₄ == ret₄₀
          || i₅₀ < 5
          || i₄₄ < 5 - 1
          || i₄₁ < 5
          || i₃₅ < 5
          || i₂₉ < 5));

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, ret₄₉: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 5
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                        i₁₁ < 5
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
                 ==> i₁₁ < 5))
        && 0 <= i₃₅
        && i₃₅ <= 5
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₅
                 ==> i₂ < 5))
        && 0 <= i₄₁
        && i₄₁ <= 5
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₁
                 ==> i₂ < 5))
        && 0 <= i₄₄
        && i₄₄ <= 4
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> (exists i₁₇: int ::
                        i₁₇ < 4
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
                 ==> i₁₇ < 4))
        && 0 <= i₅₀
        && i₅₀ <= 5
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₅₀
                 ==> i₂ < 5))
         ==> ret₃₄ == ret₄₉
          || i₅₀ < 5
          || i₄₄ < 5 - 1
          || i₄₁ < 5
          || i₃₅ < 5
          || i₂₉ < 5));

