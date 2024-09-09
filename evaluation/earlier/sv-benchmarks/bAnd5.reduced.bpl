data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₃₃: int, x: [int]int, x₃₄: [int]int, i₃₅: int, res₃₉: int, i₄₀: int, res₄₅: int, i₄₆: int, x₄₈: [int]int, i₄₉: int, i₅₅: int ::
      (  1 < N₃₃
        && 0 <= i₃₅
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₅
                 ==> (exists __VERIFIER_nondet_int₂₁₃: int ::
                        i₁₄ < N₃₃
                        && x₃₄[i₁₄] == __VERIFIER_nondet_int₂₁₃)))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₃₅
                || x₃₄[i₁₄] == x[i₁₄])
        && 1 <= i₄₀
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₀
                 ==> i₄ < N₃₃))
        && 1 <= i₄₆
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₆
                 ==> i₄ < N₃₃))
        && 0 <= i₄₉
        && (forall i₂₃: int ::
              (  0 <= i₂₃
                && i₂₃ < i₄₉
                 ==> i₂₃ < -1 + N₃₃
                  && x₄₈[i₂₃] == x₃₄[0 := x₃₄[1]][1 := x₃₄[0]][1 + i₂₃]))
        && (forall i₂₃: int ::
                  0 <= i₂₃
                  && i₂₃ < i₄₉
                || x₄₈[i₂₃] == x₃₄[0 := x₃₄[1]][1 := x₃₄[0]][i₂₃])
        && 1 <= i₅₅
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₅₅
                 ==> i₄ < N₃₃))
         ==> res₃₉ == res₄₅
          || i₅₅ < N₃₃
          || i₄₉ < N₃₃ - 1
          || i₄₆ < N₃₃
          || i₄₀ < N₃₃
          || i₃₅ < N₃₃));

goal (forall N₃₃: int, x: [int]int, x₃₄: [int]int, i₃₅: int, res₃₉: int, i₄₀: int, i₄₆: int, x₄₈: [int]int, i₄₉: int, res₅₄: int, i₅₅: int ::
      (  1 < N₃₃
        && 0 <= i₃₅
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₅
                 ==> (exists __VERIFIER_nondet_int₂₁₃: int ::
                        i₁₄ < N₃₃
                        && x₃₄[i₁₄] == __VERIFIER_nondet_int₂₁₃)))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₃₅
                || x₃₄[i₁₄] == x[i₁₄])
        && 1 <= i₄₀
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₀
                 ==> i₄ < N₃₃))
        && 1 <= i₄₆
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₄₆
                 ==> i₄ < N₃₃))
        && 0 <= i₄₉
        && (forall i₂₃: int ::
              (  0 <= i₂₃
                && i₂₃ < i₄₉
                 ==> i₂₃ < -1 + N₃₃
                  && x₄₈[i₂₃] == x₃₄[0 := x₃₄[1]][1 := x₃₄[0]][1 + i₂₃]))
        && (forall i₂₃: int ::
                  0 <= i₂₃
                  && i₂₃ < i₄₉
                || x₄₈[i₂₃] == x₃₄[0 := x₃₄[1]][1 := x₃₄[0]][i₂₃])
        && 1 <= i₅₅
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₅₅
                 ==> i₄ < N₃₃))
         ==> res₃₉ == res₅₄
          || i₅₅ < N₃₃
          || i₄₉ < N₃₃ - 1
          || i₄₆ < N₃₃
          || i₄₀ < N₃₃
          || i₃₅ < N₃₃));

