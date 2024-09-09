data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall ARR_SIZE₂₂: int, array1: [int]int, array2: [int]int, array1₂₃: [int]int, array2₂₄: [int]int, count₂₅: int, index₁₀: int, temp₁₁: int ::
      (  0 < ARR_SIZE₂₂
        && 0 <= count₂₅
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₅
                 ==> count₆ < ARR_SIZE₂₂
                  && array1₂₃[count₆] == 0
                  && array2₂₄[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₅
                ||   array1₂₃[count₆] == array1[count₆]
                  && array2₂₄[count₆] == array2[count₆])
        && temp₁₁ == 0
        && 0 <= index₁₀
        && index₁₀ < ARR_SIZE₂₂
         ==> count₂₅ < ARR_SIZE₂₂));

