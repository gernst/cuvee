data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₄: [int]int, array2₂₅: [int]int, count₂₆: int, nondet_short₃₁₀: int, temp₁₂: int ::
      (  0 < nondet_short₁
        && 0 <= count₂₆
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₆
                 ==> count₆ < nondet_short₁
                  && array1₂₄[count₆] == 0
                  && array2₂₅[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₆
                ||   array1₂₄[count₆] == array1[count₆]
                  && array2₂₅[count₆] == array2[count₆])
        && temp₁₂ == 0
        && 0 <= nondet_short₃₁₀
        && nondet_short₃₁₀ < nondet_short₁
         ==> count₂₆ < nondet_short₁
          || nondet_short₃₁₀ % 2 == 0));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₄: [int]int, array2₂₅: [int]int, count₂₆: int, nondet_short₃₁₀: int, temp₁₃: int ::
      (  0 < nondet_short₁
        && 0 <= count₂₆
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₆
                 ==> count₆ < nondet_short₁
                  && array1₂₄[count₆] == 0
                  && array2₂₅[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₆
                ||   array1₂₄[count₆] == array1[count₆]
                  && array2₂₅[count₆] == array2[count₆])
        && temp₁₃ == 0
        && nondet_short₃₁₀ % 2 == 0
        && 0 <= nondet_short₃₁₀
        && nondet_short₃₁₀ < nondet_short₁
         ==> count₂₆ < nondet_short₁));

