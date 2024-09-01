data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall src: [int]int, dst: [int]int, src₁₄: [int]int, j₁₅: int, dst₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  0 <= j₁₅
        && j₁₅ <= 100000
        && (forall x₅: int, j₄: int ::
              (  x₅ == j₄
                && 0 <= j₄
                && j₄ < j₁₅
                 ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                        j₄ < 100000
                        && x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₅
                        && src₁₄[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists j₄: int ::
                        x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₅)
                || src₁₄[x₅] == src[x₅])
        && (forall j₄: int ::
              (  j₄ <= j₄
                && 0 <= j₄
                && j₄ < j₁₅
                 ==> j₄ < 100000))
        && 0 <= i₁₇
        && i₁₇ <= 100000
        && (forall x₉: int, i₈: int ::
              (  x₉ == i₈
                && 0 <= i₈
                && i₈ < i₁₇
                 ==> (exists i₈: int ::
                        i₈ < 100000
                        && (src₁₄[i₈] == 0
                           ==> false))))
        && (forall x₉: int ::
                (exists i₈: int ::
                        x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i₁₇)
                || dst₁₆[x₉] == dst[x₉])
        && (forall i₈: int ::
              (  i₈ <= i₈
                && 0 <= i₈
                && i₈ < i₁₇
                 ==> i₈ < 100000
                  && (src₁₄[i₈] == 0
                     ==> false)))
        && 0 <= i₁₈
        && i₁₈ <= 100000
        && (forall i₁₂: int ::
              (  i₁₂ <= i₁₂
                && 0 <= i₁₂
                && i₁₂ < i₁₈
                 ==> i₁₂ < 100000
                  && (src₁₄[i₁₂] == 0
                     ==> false)))
        && i₁₈ < 100000
         ==> src₁₄[i₁₈] == 0
          || i₁₇ < 100000
          || j₁₅ < 100000
          || dst₁₆[i₁₈] == src₁₄[i₁₈]));

goal (forall src: [int]int, dst: [int]int, src₁₄: [int]int, j₁₅: int, dst₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  0 <= j₁₅
        && j₁₅ <= 100000
        && (forall x₅: int, j₄: int ::
              (  x₅ == j₄
                && 0 <= j₄
                && j₄ < j₁₅
                 ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                        j₄ < 100000
                        && x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₅
                        && src₁₄[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists j₄: int ::
                        x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₅)
                || src₁₄[x₅] == src[x₅])
        && (forall j₄: int ::
              (  j₄ <= j₄
                && 0 <= j₄
                && j₄ < j₁₅
                 ==> j₄ < 100000))
        && 0 <= i₁₇
        && i₁₇ <= 100000
        && (forall x₉: int, i₈: int ::
              (  x₉ == i₈
                && 0 <= i₈
                && i₈ < i₁₇
                 ==> (exists i₈: int ::
                        i₈ < 100000
                        && (src₁₄[i₈] == 0
                           ==> false))))
        && (forall x₉: int ::
                (exists i₈: int ::
                        x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i₁₇)
                || dst₁₆[x₉] == dst[x₉])
        && (forall i₈: int ::
              (  i₈ <= i₈
                && 0 <= i₈
                && i₈ < i₁₇
                 ==> i₈ < 100000
                  && (src₁₄[i₈] == 0
                     ==> false)))
        && src₁₄[i₁₇] == 0
        && 0 <= i₁₈
        && i₁₈ <= 100000
        && (forall i₁₂: int ::
              (  i₁₂ <= i₁₂
                && 0 <= i₁₂
                && i₁₂ < i₁₈
                 ==> i₁₂ < 100000
                  && (src₁₄[i₁₂] == 0
                     ==> false)))
        && i₁₈ < 100000
         ==> src₁₄[i₁₈] == 0
          || j₁₅ < 100000
          || dst₁₆[i₁₈] == src₁₄[i₁₈]));

