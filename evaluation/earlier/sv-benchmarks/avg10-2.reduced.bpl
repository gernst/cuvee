data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, ret₄₀: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 10
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 10
                        && x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₉
                        && x₂₈[x₁₄] == __VERIFIER_nondet_int₂₁₂)))
        && (forall x₁₄: int ::
                (exists i₁₃: int ::
                        x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₉)
                || x₂₈[x₁₄] == x[x₁₄])
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> i₁₃ < 10))
        && 0 <= i₃₅
        && i₃₅ <= 10
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₅
                 ==> i₄ < 10))
        && 0 <= i₄₁
        && i₄₁ <= 10
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < 10))
        && 0 <= i₄₄
        && i₄₄ <= 9
        && (forall x₂₀: int, i₁₉: int ::
              (  x₂₀ == i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₄₄
                 ==> (exists i₁₉: int ::
                        i₁₉ < 9
                        && x₂₀ == i₁₉
                        && 0 <= i₁₉
                        && i₁₉ < i₄₄
                        && x₄₃[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
        && (forall x₂₀: int ::
                (exists i₁₉: int ::
                        x₂₀ == i₁₉
                        && 0 <= i₁₉
                        && i₁₉ < i₄₄)
                || x₄₃[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀])
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₄₄
                 ==> i₁₉ < 9))
        && 0 <= i₅₀
        && i₅₀ <= 10
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₅₀
                 ==> i₄ < 10))
         ==> ret₃₄ / 10 == ret₄₀ / 10
          || i₅₀ < 10
          || i₄₄ < 10 - 1
          || i₄₁ < 10
          || i₃₅ < 10
          || i₂₉ < 10));

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, ret₄₉: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 10
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 10
                        && x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₉
                        && x₂₈[x₁₄] == __VERIFIER_nondet_int₂₁₂)))
        && (forall x₁₄: int ::
                (exists i₁₃: int ::
                        x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₉)
                || x₂₈[x₁₄] == x[x₁₄])
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> i₁₃ < 10))
        && 0 <= i₃₅
        && i₃₅ <= 10
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₅
                 ==> i₄ < 10))
        && 0 <= i₄₁
        && i₄₁ <= 10
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < 10))
        && 0 <= i₄₄
        && i₄₄ <= 9
        && (forall x₂₀: int, i₁₉: int ::
              (  x₂₀ == i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₄₄
                 ==> (exists i₁₉: int ::
                        i₁₉ < 9
                        && x₂₀ == i₁₉
                        && 0 <= i₁₉
                        && i₁₉ < i₄₄
                        && x₄₃[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
        && (forall x₂₀: int ::
                (exists i₁₉: int ::
                        x₂₀ == i₁₉
                        && 0 <= i₁₉
                        && i₁₉ < i₄₄)
                || x₄₃[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀])
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₄₄
                 ==> i₁₉ < 9))
        && 0 <= i₅₀
        && i₅₀ <= 10
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₅₀
                 ==> i₄ < 10))
         ==> ret₃₄ / 10 == ret₄₉ / 10
          || i₅₀ < 10
          || i₄₄ < 10 - 1
          || i₄₁ < 10
          || i₃₅ < 10
          || i₂₉ < 10));

