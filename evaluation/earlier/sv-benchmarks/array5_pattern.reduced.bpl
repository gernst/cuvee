data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₇: [int]int, array2₂₈: [int]int, count₂₉: int, count₁₇: int ::
      (  0 < nondet_short₁
        && 0 <= count₂₉
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₉
                 ==> count₆ < nondet_short₁
                  && array1₂₇[count₆] == 0
                  && array2₂₈[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₉
                ||   array1₂₇[count₆] == array1[count₆]
                  && array2₂₈[count₆] == array2[count₆])
         ==> count₂₉ < nondet_short₁
          || (exists index₁₀: int, temp₁₁: int ::
                  (temp₁₁ == 0
                     ==> false)
                  && count₁₇ == 200
                  && index₁₀ % 2 == 0
                  && 0 <= index₁₀
                  && index₁₀ < nondet_short₁
                  && array2₂₈[index₁₀] == (-1) * count₁₇
                  && array1₂₇[index₁₀] == (-1) * (-1) * count₁₇)
          || (exists index₁₀: int, temp₁₂: int ::
                  (temp₁₂ == 0
                     ==> false)
                  && count₁₇ == 200
                  && (index₁₀ % 2 == 0
                     ==> false)
                  && 0 <= index₁₀
                  && index₁₀ < nondet_short₁
                  && array2₂₈[index₁₀] == (-1) * (-1) * count₁₇
                  && array1₂₇[index₁₀] == (-1) * count₁₇)
          || (exists index₁₀: int, temp₁₃: int ::
                  (temp₁₃ == 0
                     ==> false)
                  && (count₁₇ == 200
                     ==> false)
                  && index₁₀ % 2 == 0
                  && 0 <= index₁₀
                  && index₁₀ < nondet_short₁
                  && array2₂₈[index₁₀] == (-1) * count₁₇
                  && array1₂₇[index₁₀] == (-1) * (-1) * count₁₇)
          || (exists index₁₀: int, temp₁₄: int ::
                  (temp₁₄ == 0
                     ==> false)
                  && (count₁₇ == 200
                     ==> false)
                  && (index₁₀ % 2 == 0
                     ==> false)
                  && 0 <= index₁₀
                  && index₁₀ < nondet_short₁
                  && array2₂₈[index₁₀] == (-1) * (-1) * count₁₇
                  && array1₂₇[index₁₀] == (-1) * count₁₇)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₇: [int]int, array2₂₈: [int]int, count₂₉: int, count₁₇: int, index₁₀: int, temp₁₁: int ::
      (  0 < nondet_short₁
        && 0 <= count₂₉
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₉
                 ==> count₆ < nondet_short₁
                  && array1₂₇[count₆] == 0
                  && array2₂₈[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₉
                ||   array1₂₇[count₆] == array1[count₆]
                  && array2₂₈[count₆] == array2[count₆])
        && temp₁₁ == 0
        && count₁₇ == 200
        && index₁₀ % 2 == 0
        && 0 <= index₁₀
        && index₁₀ < nondet_short₁
         ==> count₂₉ < nondet_short₁));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₇: [int]int, array2₂₈: [int]int, count₂₉: int, count₁₇: int, index₁₀: int, temp₁₂: int ::
      (  0 < nondet_short₁
        && 0 <= count₂₉
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₉
                 ==> count₆ < nondet_short₁
                  && array1₂₇[count₆] == 0
                  && array2₂₈[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₉
                ||   array1₂₇[count₆] == array1[count₆]
                  && array2₂₈[count₆] == array2[count₆])
        && temp₁₂ == 0
        && count₁₇ == 200
        && 0 <= index₁₀
        && index₁₀ < nondet_short₁
         ==> count₂₉ < nondet_short₁
          || index₁₀ % 2 == 0));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₇: [int]int, array2₂₈: [int]int, count₂₉: int, count₁₇: int, index₁₀: int, temp₁₃: int ::
      (  0 < nondet_short₁
        && 0 <= count₂₉
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₉
                 ==> count₆ < nondet_short₁
                  && array1₂₇[count₆] == 0
                  && array2₂₈[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₉
                ||   array1₂₇[count₆] == array1[count₆]
                  && array2₂₈[count₆] == array2[count₆])
        && temp₁₃ == 0
        && index₁₀ % 2 == 0
        && 0 <= index₁₀
        && index₁₀ < nondet_short₁
         ==> count₂₉ < nondet_short₁
          || count₁₇ == 200));

goal {:named "invariant entry"} (forall nondet_short₁: int, array1: [int]int, array2: [int]int, array1₂₇: [int]int, array2₂₈: [int]int, count₂₉: int, count₁₇: int, index₁₀: int, temp₁₄: int ::
      (  0 < nondet_short₁
        && 0 <= count₂₉
        && (forall count₆: int ::
              (  0 <= count₆
                && count₆ < count₂₉
                 ==> count₆ < nondet_short₁
                  && array1₂₇[count₆] == 0
                  && array2₂₈[count₆] == 0))
        && (forall count₆: int ::
                  0 <= count₆
                  && count₆ < count₂₉
                ||   array1₂₇[count₆] == array1[count₆]
                  && array2₂₈[count₆] == array2[count₆])
        && temp₁₄ == 0
        && 0 <= index₁₀
        && index₁₀ < nondet_short₁
         ==> count₂₉ < nondet_short₁
          || index₁₀ % 2 == 0
          || count₁₇ == 200));

