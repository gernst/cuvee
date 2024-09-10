data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₄: [int]int, array2₂₅: [int]int, count₂₆: int, nondet_short₃₁₀: int, temp₁₂: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
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
        && -2147483648 <= temp₁₂
        && temp₁₂ < 2147483648
        && nondet_short₃₁₀ == -1 + nondet_short₁
        && 0 <= nondet_short₃₁₀
        && nondet_short₃₁₀ < nondet_short₁
        && -32768 <= nondet_short₃₁₀
        && nondet_short₃₁₀ < 32768
         ==> count₂₆ < nondet_short₁));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₄: [int]int, array2₂₅: [int]int, count₂₆: int, nondet_short₃₁₀: int, temp₁₃: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
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
        && -2147483648 <= temp₁₃
        && temp₁₃ < 2147483648
        && 0 <= nondet_short₃₁₀
        && nondet_short₃₁₀ < nondet_short₁
        && -32768 <= nondet_short₃₁₀
        && nondet_short₃₁₀ < 32768
         ==> count₂₆ < nondet_short₁
          || nondet_short₃₁₀ == -1 + nondet_short₁));

