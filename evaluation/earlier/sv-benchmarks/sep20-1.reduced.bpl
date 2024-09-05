data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, ret₄₀: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 20
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                        i₁₁ < 20
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
                 ==> i₁₁ < 20))
        && 0 <= i₃₅
        && i₃₅ <= 20
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₅
                 ==> i₂ < 20))
        && 0 <= i₄₁
        && i₄₁ <= 20
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₁
                 ==> i₂ < 20))
        && 0 <= i₄₄
        && i₄₄ <= 19
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> (exists i₁₇: int ::
                        i₁₇ < 19
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
                 ==> i₁₇ < 19))
        && 0 <= i₅₀
        && i₅₀ <= 20
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₅₀
                 ==> i₂ < 20))
         ==> ret₃₄ == ret₄₀
          || i₅₀ < 20
          || i₄₄ < 20 - 1
          || i₄₁ < 20
          || i₃₅ < 20
          || i₂₉ < 20));

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, ret₄₉: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 20
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                        i₁₁ < 20
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
                 ==> i₁₁ < 20))
        && 0 <= i₃₅
        && i₃₅ <= 20
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₃₅
                 ==> i₂ < 20))
        && 0 <= i₄₁
        && i₄₁ <= 20
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₄₁
                 ==> i₂ < 20))
        && 0 <= i₄₄
        && i₄₄ <= 19
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> (exists i₁₇: int ::
                        i₁₇ < 19
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
                 ==> i₁₇ < 19))
        && 0 <= i₅₀
        && i₅₀ <= 20
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < i₅₀
                 ==> i₂ < 20))
         ==> ret₃₄ == ret₄₉
          || i₅₀ < 20
          || i₄₄ < 20 - 1
          || i₄₁ < 20
          || i₃₅ < 20
          || i₂₉ < 20));

