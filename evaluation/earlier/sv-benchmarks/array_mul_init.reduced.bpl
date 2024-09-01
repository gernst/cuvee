data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, a₂₃: [int]int, b₂₄: [int]int, i₂₅: int, a₂₇: [int]int, b₂₈: [int]int, i₂₉: int, i₃₀: int ::
      (  0 <= i₂₅
        && i₂₅ <= 100000
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₅
                 ==> (exists i₅: int ::
                        i₅ < 100000
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅
                        && a₂₃[x₆] == i₅)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅)
                || a₂₃[x₆] == a[x₆])
        && (forall x₇: int, i₅: int ::
              (  x₇ == i₅
                && 0 <= i₅
                && i₅ < i₂₅
                 ==> (exists i₅: int ::
                        i₅ < 100000
                        && x₇ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅
                        && b₂₄[x₇] == i₅)))
        && (forall x₇: int ::
                (exists i₅: int ::
                        x₇ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅)
                || b₂₄[x₇] == b[x₇])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₅
                 ==> i₅ < 100000))
        && 0 <= i₂₉
        && i₂₉ <= 100000
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₉
                 ==> (exists __VERIFIER_nondet_short₂₁₁: int ::
                      (__VERIFIER_nondet_short₂₁₁ == 0
                         ==> false))))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₉)
                || a₂₇[x₁₅] == a₂₃[x₁₅])
        && (forall x₁₆: int, i₁₄: int ::
              (  x₁₆ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₉
                 ==> (exists __VERIFIER_nondet_short₂₁₁: int ::
                      (__VERIFIER_nondet_short₂₁₁ == 0
                         ==> false))))
        && (forall x₁₆: int ::
                (exists i₁₄: int ::
                        x₁₆ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₉)
                || b₂₈[x₁₆] == b₂₄[x₁₆])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₉
                 ==> i₁₄ < 100000))
        && 0 <= i₃₀
        && i₃₀ <= 100000
        && (forall i₂₁: int ::
              (  i₂₁ <= i₂₁
                && 0 <= i₂₁
                && i₂₁ < i₃₀
                 ==> i₂₁ < 100000))
        && i₃₀ < 100000
         ==> i₂₉ < 100000
          || i₂₅ < 100000
          || a₂₇[i₃₀] == b₂₈[i₃₀]
          || b₂₈[i₃₀] == a₂₇[i₃₀] * a₂₇[i₃₀]));

