data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₂: [int]int, array2₂₃: [int]int, count₂₄: int, index₁₀: int, temp₁₁: int ::
      (  0 < nondet_short₁
        && 0 <= count₂₄
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₄
                 ==> count₆ < nondet_short₁
                  && array1₂₂[count₆] == 0
                  && array2₂₃[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₄
                ||   array1₂₂[count₆] == array1[count₆]
                  && array2₂₃[count₆] == array2[count₆])
        && temp₁₁ == 0
        && 0 <= index₁₀
        && index₁₀ < nondet_short₁
         ==> count₂₄ < nondet_short₁));

