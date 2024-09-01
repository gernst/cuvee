data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, b₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, j₂₂: int, i₂₃: int, j₂₄: int ::
      (  0 <= i₁₉
        && i₁₉ <= 10000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 10000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉
                        && b₁₈[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉)
                || b₁₈[x₅] == b[x₅])
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> i₄ < 10000))
        && 0 <= i₂₁
        && 0 <= j₂₂
        && i₂₁ <= 10000
        && (forall x₁₀: int, j₉: int ::
              (  x₁₀ == j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> (exists i₈: int, j₉: int ::
                        i₈ < 10000
                        && x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂
                        && a₂₀[x₁₀] == b₁₈[i₈])))
        && (forall x₁₀: int ::
                (exists j₉: int ::
                        x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂)
                || a₂₀[x₁₀] == a[x₁₀])
        && (forall i₈: int, j₉: int ::
              (  i₈ <= i₈
                && j₉ <= j₉
                && 0 <= i₈
                && i₈ < i₂₁
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> i₈ < 10000))
        && 0 <= i₂₃
        && 0 <= j₂₄
        && i₂₃ <= 10000
        && (forall i₁₄: int, j₁₅: int ::
              (  i₁₄ <= i₁₄
                && j₁₅ <= j₁₅
                && 0 <= i₁₄
                && i₁₄ < i₂₃
                && 0 <= j₁₅
                && j₁₅ < j₂₄
                 ==> i₁₄ < 10000))
        && i₂₃ < 10000
         ==> i₂₁ < 10000
          || i₁₉ < 10000
          || a₂₀[j₂₄] == b₁₈[j₂₄]));

