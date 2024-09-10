data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₄: [int]int, array2₂₅: [int]int, count₂₆: int ::
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
         ==> count₂₆ < nondet_short₁
          || (exists index₁₀: int, temp₁₂: int ::
                  (temp₁₂ == 0
                     ==> false)
                  && index₁₀ % 2 == 0
                  && 0 <= index₁₀
                  && index₁₀ < nondet_short₁
                  && array1₂₄[index₁₀] == (-1) * (-1) * 1)
          || (exists index₁₀: int, temp₁₃: int ::
                  (temp₁₃ == 0
                     ==> false)
                  && (index₁₀ % 2 == 0
                     ==> false)
                  && 0 <= index₁₀
                  && index₁₀ < nondet_short₁
                  && array1₂₄[index₁₀] == (-1) * (-1) * 1
                  && array2₂₅[index₁₀] == (-1) * 1)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₄: [int]int, array2₂₅: [int]int, count₂₆: int, index₁₀: int, temp₁₂: int ::
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
        && index₁₀ % 2 == 0
        && 0 <= index₁₀
        && index₁₀ < nondet_short₁
         ==> count₂₆ < nondet_short₁));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₄: [int]int, array2₂₅: [int]int, count₂₆: int, index₁₀: int, temp₁₃: int ::
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
        && 0 <= index₁₀
        && index₁₀ < nondet_short₁
         ==> count₂₆ < nondet_short₁
          || index₁₀ % 2 == 0));

