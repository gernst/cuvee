data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, a₁₆: [int]int, i₁₇: int, b₁₈: [int]int, i₁₉: int, f₂₀: int, i₂₁: int ::
      (  0 <= i₁₇
        && i₁₇ <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₇
                        && a₁₆[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₇)
                || a₁₆[x₅] == a[x₅])
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> i₄ < 100000))
        && 0 <= i₁₉
        && i₁₉ <= 100000
        && (forall x₉: int, i₈: int ::
              (  x₉ == i₈
                && 0 <= i₈
                && i₈ < i₁₉
                 ==> (exists i₈: int ::
                          0 <= a₁₆[i₈]
                          && i₈ < 100000
                          && x₉ == i₈
                          && 0 <= i₈
                          && i₈ < i₁₉
                          && b₁₈[x₉] == 1)
                  || (exists i₈: int ::
                        (0 <= a₁₆[i₈]
                           ==> false))))
        && (forall x₉: int ::
                (exists i₈: int ::
                        x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i₁₉)
                || b₁₈[x₉] == b[x₉])
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₉
                 ==> i₈ < 100000))
        && 0 <= i₂₁
        && i₂₁ <= 100000
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₁
                 ==> i₁₃ < 100000))
        && f₂₀ == 0
         ==> i₂₁ < 100000
          || i₁₉ < 100000
          || i₁₇ < 100000));

