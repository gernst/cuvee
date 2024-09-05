data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, ret₄₀: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 40
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 40
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
                 ==> i₁₃ < 40))
        && 0 <= i₃₅
        && i₃₅ <= 40
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₅
                 ==> i₄ < 40))
        && 0 <= i₄₁
        && i₄₁ <= 40
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < 40))
        && 0 <= i₄₄
        && i₄₄ <= 39
        && (forall x₂₀: int, i₁₉: int ::
              (  x₂₀ == i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₄₄
                 ==> (exists i₁₉: int ::
                        i₁₉ < 39
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
                 ==> i₁₉ < 39))
        && 0 <= i₅₀
        && i₅₀ <= 40
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₅₀
                 ==> i₄ < 40))
         ==> ret₃₄ == ret₄₀
          || i₅₀ < 40
          || i₄₄ < 40 - 1
          || i₄₁ < 40
          || i₃₅ < 40
          || i₂₉ < 40));

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, ret₄₉: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 40
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 40
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
                 ==> i₁₃ < 40))
        && 0 <= i₃₅
        && i₃₅ <= 40
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₅
                 ==> i₄ < 40))
        && 0 <= i₄₁
        && i₄₁ <= 40
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < 40))
        && 0 <= i₄₄
        && i₄₄ <= 39
        && (forall x₂₀: int, i₁₉: int ::
              (  x₂₀ == i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₄₄
                 ==> (exists i₁₉: int ::
                        i₁₉ < 39
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
                 ==> i₁₉ < 39))
        && 0 <= i₅₀
        && i₅₀ <= 40
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₅₀
                 ==> i₄ < 40))
         ==> ret₃₄ == ret₄₉
          || i₅₀ < 40
          || i₄₄ < 40 - 1
          || i₄₁ < 40
          || i₃₅ < 40
          || i₂₉ < 40));

