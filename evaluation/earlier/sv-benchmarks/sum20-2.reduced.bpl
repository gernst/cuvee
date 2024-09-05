data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, ret₄₀: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 20
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 20
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
                 ==> i₁₃ < 20))
        && 0 <= i₃₅
        && i₃₅ <= 20
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₅
                 ==> i₄ < 20))
        && 0 <= i₄₁
        && i₄₁ <= 20
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < 20))
        && 0 <= i₄₄
        && i₄₄ <= 19
        && (forall x₂₀: int, i₁₉: int ::
              (  x₂₀ == i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₄₄
                 ==> (exists i₁₉: int ::
                        i₁₉ < 19
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
                 ==> i₁₉ < 19))
        && 0 <= i₅₀
        && i₅₀ <= 20
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₅₀
                 ==> i₄ < 20))
         ==> ret₃₄ == ret₄₀
          || i₅₀ < 20
          || i₄₄ < 20 - 1
          || i₄₁ < 20
          || i₃₅ < 20
          || i₂₉ < 20));

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, ret₃₄: int, i₃₅: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, ret₄₉: int, i₅₀: int ::
      (  0 <= i₂₉
        && i₂₉ <= 20
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 20
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
                 ==> i₁₃ < 20))
        && 0 <= i₃₅
        && i₃₅ <= 20
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₅
                 ==> i₄ < 20))
        && 0 <= i₄₁
        && i₄₁ <= 20
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < 20))
        && 0 <= i₄₄
        && i₄₄ <= 19
        && (forall x₂₀: int, i₁₉: int ::
              (  x₂₀ == i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₄₄
                 ==> (exists i₁₉: int ::
                        i₁₉ < 19
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
                 ==> i₁₉ < 19))
        && 0 <= i₅₀
        && i₅₀ <= 20
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₅₀
                 ==> i₄ < 20))
         ==> ret₃₄ == ret₄₉
          || i₅₀ < 20
          || i₄₄ < 20 - 1
          || i₄₁ < 20
          || i₃₅ < 20
          || i₂₉ < 20));

