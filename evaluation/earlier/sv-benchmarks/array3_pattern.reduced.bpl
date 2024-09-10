data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₃₀: [int]int, array2₃₁: [int]int, count₃₂: int, index₁₀: int, temp₁₁: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= count₃₂
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₃₂
                 ==> count₆ < nondet_short₁
                  && array1₃₀[count₆] == 0
                  && array2₃₁[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₃₂
                ||   array1₃₀[count₆] == array1[count₆]
                  && array2₃₁[count₆] == array2[count₆])
        && temp₁₁ == 0
        && -2147483648 <= temp₁₁
        && temp₁₁ < 2147483648
        && 0 <= index₁₀
        && index₁₀ < nondet_short₁
        && -32768 <= index₁₀
        && index₁₀ < 32768
         ==> count₃₂ < nondet_short₁));

