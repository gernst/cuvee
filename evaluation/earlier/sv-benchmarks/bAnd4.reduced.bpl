data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, res₃₃: int, i₃₄: int, res₃₉: int, i₄₀: int, x₄₂: [int]int, i₄₃: int, i₄₉: int ::
      (  0 <= i₂₉
        && i₂₉ <= 100000
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 100000
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
                 ==> i₁₃ < 100000))
        && 1 <= i₃₄
        && i₃₄ <= 100000
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₄
                 ==> i₄ < 100000))
        && 1 <= i₄₀
        && i₄₀ <= 100000
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₀
                 ==> i₄ < 100000))
        && 0 <= i₄₃
        && i₄₃ <= 99999
        && (forall x₂₀: int, i₁₉: int ::
              (  x₂₀ == i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₄₃
                 ==> (exists i₁₉: int ::
                        i₁₉ < 99999
                        && x₂₀ == i₁₉
                        && 0 <= i₁₉
                        && i₁₉ < i₄₃
                        && x₄₂[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
        && (forall x₂₀: int ::
                (exists i₁₉: int ::
                        x₂₀ == i₁₉
                        && 0 <= i₁₉
                        && i₁₉ < i₄₃)
                || x₄₂[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀])
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₄₃
                 ==> i₁₉ < 99999))
        && 1 <= i₄₉
        && i₄₉ <= 100000
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₉
                 ==> i₄ < 100000))
         ==> res₃₃ == res₃₉
          || i₄₉ < 100000
          || i₄₃ < 100000 - 1
          || i₄₀ < 100000
          || i₃₄ < 100000
          || i₂₉ < 100000));

goal (forall x: [int]int, x₂₈: [int]int, i₂₉: int, res₃₃: int, i₃₄: int, i₄₀: int, x₄₂: [int]int, i₄₃: int, res₄₈: int, i₄₉: int ::
      (  0 <= i₂₉
        && i₂₉ <= 100000
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 100000
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
                 ==> i₁₃ < 100000))
        && 1 <= i₃₄
        && i₃₄ <= 100000
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₃₄
                 ==> i₄ < 100000))
        && 1 <= i₄₀
        && i₄₀ <= 100000
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₀
                 ==> i₄ < 100000))
        && 0 <= i₄₃
        && i₄₃ <= 99999
        && (forall x₂₀: int, i₁₉: int ::
              (  x₂₀ == i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₄₃
                 ==> (exists i₁₉: int ::
                        i₁₉ < 99999
                        && x₂₀ == i₁₉
                        && 0 <= i₁₉
                        && i₁₉ < i₄₃
                        && x₄₂[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
        && (forall x₂₀: int ::
                (exists i₁₉: int ::
                        x₂₀ == i₁₉
                        && 0 <= i₁₉
                        && i₁₉ < i₄₃)
                || x₄₂[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀])
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₄₃
                 ==> i₁₉ < 99999))
        && 1 <= i₄₉
        && i₄₉ <= 100000
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₉
                 ==> i₄ < 100000))
         ==> res₃₃ == res₄₈
          || i₄₉ < 100000
          || i₄₃ < 100000 - 1
          || i₄₀ < 100000
          || i₃₄ < 100000
          || i₂₉ < 100000));

