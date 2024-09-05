data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int, a1₂₈: [int]int, a2₂₉: [int]int, a3₃₀: [int]int, i₃₁: int, a2₃₂: [int]int, i₃₃: int, a3₃₄: [int]int, i₃₅: int, x₃₆: int ::
      (  0 <= i₃₁
        && i₃₁ <= 200000
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₃₁
                 ==> (exists __VERIFIER_nondet_int₁₆: int, i₉: int ::
                        i₉ < 200000
                        && x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₃₁
                        && a1₂₈[x₁₀] == __VERIFIER_nondet_int₁₆)))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₃₁)
                || a1₂₈[x₁₀] == a1[x₁₀])
        && (forall x₁₁: int, i₉: int ::
              (  x₁₁ == i₉
                && 0 <= i₉
                && i₉ < i₃₁
                 ==> (exists __VERIFIER_nondet_int₂₇: int, i₉: int ::
                        i₉ < 200000
                        && x₁₁ == i₉
                        && 0 <= i₉
                        && i₉ < i₃₁
                        && a2₂₉[x₁₁] == __VERIFIER_nondet_int₂₇)))
        && (forall x₁₁: int ::
                (exists i₉: int ::
                        x₁₁ == i₉
                        && 0 <= i₉
                        && i₉ < i₃₁)
                || a2₂₉[x₁₁] == a2[x₁₁])
        && (forall x₁₂: int, i₉: int ::
              (  x₁₂ == i₉
                && 0 <= i₉
                && i₉ < i₃₁
                 ==> (exists __VERIFIER_nondet_int₃₈: int, i₉: int ::
                        i₉ < 200000
                        && x₁₂ == i₉
                        && 0 <= i₉
                        && i₉ < i₃₁
                        && a3₃₀[x₁₂] == __VERIFIER_nondet_int₃₈)))
        && (forall x₁₂: int ::
                (exists i₉: int ::
                        x₁₂ == i₉
                        && 0 <= i₉
                        && i₉ < i₃₁)
                || a3₃₀[x₁₂] == a3[x₁₂])
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₃₁
                 ==> i₉ < 200000))
        && 0 <= i₃₃
        && i₃₃ <= 200000
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> (exists i₁₇: int ::
                      (i₁₇ == 150000
                         ==> false))))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₃)
                || a2₃₂[x₁₈] == a2₂₉[x₁₈])
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> i₁₇ < 200000))
        && 0 <= i₃₅
        && i₃₅ <= 200000
        && (forall x₂₂: int, i₂₁: int ::
              (  x₂₂ == i₂₁
                && 0 <= i₂₁
                && i₂₁ < i₃₅
                 ==> (exists i₂₁: int ::
                        (i₂₁ == 150000
                           ==> false))
                  || (exists i₂₁: int ::
                          i₂₁ == 150000
                          && i₂₁ < 200000
                          && x₂₂ == i₂₁
                          && 0 <= i₂₁
                          && i₂₁ < i₃₅
                          && a3₃₄[x₂₂] == a1₂₈[i₂₁])))
        && (forall x₂₂: int ::
                (exists i₂₁: int ::
                        x₂₂ == i₂₁
                        && 0 <= i₂₁
                        && i₂₁ < i₃₅)
                || a3₃₄[x₂₂] == a3₃₀[x₂₂])
        && (forall i₂₁: int ::
              (  0 <= i₂₁
                && i₂₁ < i₃₅
                 ==> i₂₁ < 200000))
        && 0 <= x₃₆
        && x₃₆ <= 200000
        && (forall x₂₆: int ::
              (  0 <= x₂₆
                && x₂₆ < x₃₆
                 ==> x₂₆ < 200000))
        && x₃₆ < 200000
         ==> i₃₅ < 200000
          || i₃₃ < 200000
          || i₃₁ < 200000
          || a1₂₈[x₃₆] == a3₃₄[x₃₆]));

