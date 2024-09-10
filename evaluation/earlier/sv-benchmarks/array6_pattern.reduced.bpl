data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₂: [int]int, array2₂₃: [int]int, count₂₄: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= count₂₄
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₄
                 ==> count₆ < nondet_short₁
                  && array1₂₂[count₆] == (-1) * (-1) * count₆
                  && array2₂₃[count₆] == (-1) * count₆))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₄
                ||   array1₂₂[count₆] == array1[count₆]
                  && array2₂₃[count₆] == array2[count₆])
         ==> count₂₄ < nondet_short₁
          || (exists index₁₀: int, temp₁₁: int ::
                  (temp₁₁ == 0
                     ==> false)
                  && -2147483648 <= temp₁₁
                  && temp₁₁ < 2147483648
                  && 0 < index₁₀
                  && index₁₀ < -1 + nondet_short₁
                  && -32768 <= index₁₀
                  && index₁₀ < 32768
                  && array1₂₂[index₁₀] == array1₂₂[1 + index₁₀] + array1₂₂[-1 + index₁₀]
                  && array2₂₃[index₁₀] == array2₂₃[1 + index₁₀] + array2₂₃[-1 + index₁₀])));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₂: [int]int, array2₂₃: [int]int, count₂₄: int, index₁₀: int, temp₁₁: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= count₂₄
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₄
                 ==> count₆ < nondet_short₁
                  && array1₂₂[count₆] == (-1) * (-1) * count₆
                  && array2₂₃[count₆] == (-1) * count₆))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₄
                ||   array1₂₂[count₆] == array1[count₆]
                  && array2₂₃[count₆] == array2[count₆])
        && temp₁₁ == 0
        && -2147483648 <= temp₁₁
        && temp₁₁ < 2147483648
        && 0 < index₁₀
        && index₁₀ < -1 + nondet_short₁
        && -32768 <= index₁₀
        && index₁₀ < 32768
         ==> count₂₄ < nondet_short₁));

