data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall element: int, vectorx: [int]int, vectorx₂₃: [int]int, i₂₄: int, found₂₅: int, i₂₇: int, found₉: int, i₁₁: int ::
      (  -2147483648 <= element
        && element < 2147483648
        && 0 <= i₂₄
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₄
                 ==> (exists nondet_int₁₅: int ::
                        -2147483648 <= nondet_int₁₅
                        && nondet_int₁₅ < 2147483648
                        && i₆ < 100000
                        && vectorx₂₃[i₆] == nondet_int₁₅)))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₄
                || vectorx₂₃[i₆] == vectorx[i₆])
        && 0 <= i₂₇
        && (forall found₁₀₁: int, i₁₀₂: int ::
              (  0 <= i₁₀₂
                && i₁₀₂ < i₂₇
                 ==> vectorx₂₃[i₁₀₂] == element
                    && i₁₀₂ < 100000
                    && found₁₀₁ == 0
                  ||   (vectorx₂₃[i₁₀₂] == element
                       ==> false)
                    && i₁₀₂ < 100000
                    && found₁₀₁ == 0))
        && i₂₇ < 100000
        && found₂₅ == 0
        && vectorx₂₃[i₂₇] == element
        && 0 <= i₁₁
        && i₁₁ < i₂₇ + 1
         ==> i₂₄ < 100000
          ||   vectorx₂₃[i₁₁] == element
            && i₁₁ < 100000
            && found₉ == 0
          ||   (vectorx₂₃[i₁₁] == element
               ==> false)
            && i₁₁ < 100000
            && found₉ == 0));

goal {:named "invariant forward"} (forall element: int, vectorx: [int]int, vectorx₂₃: [int]int, i₂₄: int, found₂₅: int, i₂₇: int, found₉: int, i₁₁: int ::
      (  -2147483648 <= element
        && element < 2147483648
        && 0 <= i₂₄
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₄
                 ==> (exists nondet_int₁₅: int ::
                        -2147483648 <= nondet_int₁₅
                        && nondet_int₁₅ < 2147483648
                        && i₆ < 100000
                        && vectorx₂₃[i₆] == nondet_int₁₅)))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₄
                || vectorx₂₃[i₆] == vectorx[i₆])
        && 0 <= i₂₇
        && (forall found₁₁₇: int, i₁₁₈: int ::
              (  0 <= i₁₁₈
                && i₁₁₈ < i₂₇
                 ==> vectorx₂₃[i₁₁₈] == element
                    && i₁₁₈ < 100000
                    && found₁₁₇ == 0
                  ||   (vectorx₂₃[i₁₁₈] == element
                       ==> false)
                    && i₁₁₈ < 100000
                    && found₁₁₇ == 0))
        && i₂₇ < 100000
        && found₂₅ == 0
        && 0 <= i₁₁
        && i₁₁ < i₂₇ + 1
         ==> vectorx₂₃[i₂₇] == element
          || i₂₄ < 100000
          ||   vectorx₂₃[i₁₁] == element
            && i₁₁ < 100000
            && found₉ == 0
          ||   (vectorx₂₃[i₁₁] == element
               ==> false)
            && i₁₁ < 100000
            && found₉ == 0));

goal {:named "assert"} (forall element: int, vectorx: [int]int, vectorx₂₃: [int]int, i₂₄: int, found₂₅: int, pos₂₆: int, i₂₇: int, vectorx₂₈: [int]int, i₂₉: int, x₃₀: int ::
      (  -2147483648 <= element
        && element < 2147483648
        && 0 <= i₂₄
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₄
                 ==> (exists nondet_int₁₅: int ::
                        -2147483648 <= nondet_int₁₅
                        && nondet_int₁₅ < 2147483648
                        && i₆ < 100000
                        && vectorx₂₃[i₆] == nondet_int₁₅)))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₄
                || vectorx₂₃[i₆] == vectorx[i₆])
        && 0 <= i₂₇
        && (forall found₉: int, i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₇
                 ==> vectorx₂₃[i₁₁] == element
                    && i₁₁ < 100000
                    && found₉ == 0
                  ||   (vectorx₂₃[i₁₁] == element
                       ==> false)
                    && i₁₁ < 100000
                    && found₉ == 0))
        && pos₂₆ <= i₂₉
        && (forall i₁₅: int ::
              (  pos₂₆ <= i₁₅
                && i₁₅ < i₂₉
                 ==> i₁₅ < -1 + 100000
                  && vectorx₂₈[i₁₅] == vectorx₂₃[1 + i₁₅]))
        && (forall i₁₅: int ::
                  pos₂₆ <= i₁₅
                  && i₁₅ < i₂₉
                || vectorx₂₈[i₁₅] == vectorx₂₃[i₁₅])
        && 0 <= x₃₀
        && (forall x₂₀: int ::
              (  0 <= x₂₀
                && x₂₀ < x₃₀
                 ==> x₂₀ < pos₂₆))
        && x₃₀ < pos₂₆
        && vectorx₂₈[x₃₀] == element
         ==> found₂₅ == 0
          || i₂₉ < 100000 - 1
          || found₂₅ == 0
          || found₂₅ == 0
          || i₂₄ < 100000));

