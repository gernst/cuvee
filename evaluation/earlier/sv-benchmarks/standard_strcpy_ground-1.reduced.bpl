data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall src: [int]int, dst: [int]int, src₁₅: [int]int, j₁₆: int, dst₁₇: [int]int, i₁₈: int, x₁₉: int ::
      (  0 <= j₁₆
        && j₁₆ <= 100000
        && (forall x₅: int, j₄: int ::
              (  x₅ == j₄
                && 0 <= j₄
                && j₄ < j₁₆
                 ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                        j₄ < 100000
                        && x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₆
                        && src₁₅[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists j₄: int ::
                        x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₆)
                || src₁₅[x₅] == src[x₅])
        && (forall j₄: int ::
              (  0 <= j₄
                && j₄ < j₁₆
                 ==> j₄ < 100000))
        && 0 <= i₁₈
        && i₁₈ <= 100000
        && (forall x₉: int, i₈: int ::
              (  x₉ == i₈
                && 0 <= i₈
                && i₈ < i₁₈
                 ==> (exists i₈: int ::
                        i₈ < 100000
                        && (src₁₅[i₈] == 0
                           ==> false))))
        && (forall x₉: int ::
                (exists i₈: int ::
                        x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i₁₈)
                || dst₁₇[x₉] == dst[x₉])
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₈
                 ==> i₈ < 100000
                  && (src₁₅[i₈] == 0
                     ==> false)))
        && 0 <= x₁₉
        && x₁₉ <= i₁₈
        && (forall x₁₃: int ::
              (  0 <= x₁₃
                && x₁₃ < x₁₉
                 ==> x₁₃ < i₁₈))
        && x₁₉ < i₁₈
         ==> i₁₈ < 100000
          || j₁₆ < 100000
          || dst₁₇[x₁₉] == src₁₅[x₁₉]));

goal (forall src: [int]int, dst: [int]int, src₁₅: [int]int, j₁₆: int, dst₁₇: [int]int, i₁₈: int, x₁₉: int ::
      (  0 <= j₁₆
        && j₁₆ <= 100000
        && (forall x₅: int, j₄: int ::
              (  x₅ == j₄
                && 0 <= j₄
                && j₄ < j₁₆
                 ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                        j₄ < 100000
                        && x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₆
                        && src₁₅[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists j₄: int ::
                        x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₆)
                || src₁₅[x₅] == src[x₅])
        && (forall j₄: int ::
              (  0 <= j₄
                && j₄ < j₁₆
                 ==> j₄ < 100000))
        && 0 <= i₁₈
        && i₁₈ <= 100000
        && (forall x₉: int, i₈: int ::
              (  x₉ == i₈
                && 0 <= i₈
                && i₈ < i₁₈
                 ==> (exists i₈: int ::
                        i₈ < 100000
                        && (src₁₅[i₈] == 0
                           ==> false))))
        && (forall x₉: int ::
                (exists i₈: int ::
                        x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i₁₈)
                || dst₁₇[x₉] == dst[x₉])
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₈
                 ==> i₈ < 100000
                  && (src₁₅[i₈] == 0
                     ==> false)))
        && src₁₅[i₁₈] == 0
        && 0 <= x₁₉
        && x₁₉ <= i₁₈
        && (forall x₁₃: int ::
              (  0 <= x₁₃
                && x₁₃ < x₁₉
                 ==> x₁₃ < i₁₈))
        && x₁₉ < i₁₈
         ==> j₁₆ < 100000
          || dst₁₇[x₁₉] == src₁₅[x₁₉]));

