data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₆: [int]int, array2₂₇: [int]int, count₂₈: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= count₂₈
        && (forall count₇: int ::
              (  0 <= count₇
                && count₇ < count₂₈
                 ==> count₇ < nondet_short₁
                  && array1₂₆[count₇] == (-1) * (-1) * count₇
                  && array2₂₇[count₇] == (-1) * count₇))
        && (forall count₇: int ::
                  0 <= count₇
                  && count₇ < count₂₈
                ||   array1₂₆[count₇] == array1[count₇]
                  && array2₂₇[count₇] == array2[count₇])
         ==> count₂₈ < nondet_short₁
          || (exists nondet_short₃₁₁: int, nondet_short₄₁₂: int, temp₁₃: int ::
                  (temp₁₃ == 0
                     ==> false)
                  && -2147483648 <= temp₁₃
                  && temp₁₃ < 2147483648
                  && nondet_short₄₁₂ <= nondet_short₃₁₁
                  && nondet_short₃₁₁ < -nondet_short₄₁₂ + nondet_short₁
                  && 0 < nondet_short₄₁₂
                  && -32768 <= nondet_short₄₁₂
                  && nondet_short₄₁₂ < 32768
                  && -32768 <= nondet_short₃₁₁
                  && nondet_short₃₁₁ < 32768
                  && array2₂₇[nondet_short₃₁₁] == array2₂₇[nondet_short₃₁₁ + nondet_short₄₁₂] + array2₂₇[nondet_short₃₁₁ + -nondet_short₄₁₂]
                  && array1₂₆[nondet_short₃₁₁] == array1₂₆[nondet_short₃₁₁ + -nondet_short₄₁₂] + array1₂₆[nondet_short₃₁₁ + nondet_short₄₁₂])));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₆: [int]int, array2₂₇: [int]int, count₂₈: int, nondet_short₃₁₁: int, nondet_short₄₁₂: int, temp₁₃: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= count₂₈
        && (forall count₇: int ::
              (  0 <= count₇
                && count₇ < count₂₈
                 ==> count₇ < nondet_short₁
                  && array1₂₆[count₇] == (-1) * (-1) * count₇
                  && array2₂₇[count₇] == (-1) * count₇))
        && (forall count₇: int ::
                  0 <= count₇
                  && count₇ < count₂₈
                ||   array1₂₆[count₇] == array1[count₇]
                  && array2₂₇[count₇] == array2[count₇])
        && temp₁₃ == 0
        && -2147483648 <= temp₁₃
        && temp₁₃ < 2147483648
        && nondet_short₄₁₂ <= nondet_short₃₁₁
        && nondet_short₃₁₁ < -nondet_short₄₁₂ + nondet_short₁
        && 0 < nondet_short₄₁₂
        && -32768 <= nondet_short₄₁₂
        && nondet_short₄₁₂ < 32768
        && -32768 <= nondet_short₃₁₁
        && nondet_short₃₁₁ < 32768
         ==> count₂₈ < nondet_short₁));

