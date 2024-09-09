data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall ARR_SIZE₂₉: int, array1: [int]int, array2: [int]int, array1₃₀: [int]int, array2₃₁: [int]int, count₃₂: int, count₁₆: int ::
      (  0 < ARR_SIZE₂₉
        && 0 <= count₃₂
        && (forall count₇: int ::
              (  0 <= count₇
                && count₇ < count₃₂
                 ==> count₇ < ARR_SIZE₂₉
                  && array1₃₀[count₇] == 0
                  && array2₃₁[count₇] == 0))
        && (forall count₇: int ::
                  0 <= count₇
                  && count₇ < count₃₂
                ||   array1₃₀[count₇] == array1[count₇]
                  && array2₃₁[count₇] == array2[count₇])
         ==> count₃₂ < ARR_SIZE₂₉
          || (exists index1₁₁: int, index2₁₂: int, temp₁₃: int ::
                  (temp₁₃ == 0
                     ==> false)
                  && count₁₆ == 200
                  && array2₃₁[index2₁₂] == 0
                  && array1₃₀[index1₁₁] == 0
                  && 0 <= index2₁₂
                  && index2₁₂ < ARR_SIZE₂₉
                  && 0 <= index1₁₁
                  && index1₁₁ < ARR_SIZE₂₉
                  && array2₃₁[index2₁₂] == (-1) * count₁₆
                  && array1₃₀[index1₁₁] == (-1) * (-1) * count₁₆)
          || (exists index1₁₁: int, index2₁₂: int, temp₁₄: int ::
                  (temp₁₄ == 0
                     ==> false)
                  && (count₁₆ == 200
                     ==> false)
                  && array2₃₁[index2₁₂] == 0
                  && array1₃₀[index1₁₁] == 0
                  && 0 <= index2₁₂
                  && index2₁₂ < ARR_SIZE₂₉
                  && 0 <= index1₁₁
                  && index1₁₁ < ARR_SIZE₂₉
                  && array2₃₁[index2₁₂] == (-1) * count₁₆
                  && array1₃₀[index1₁₁] == (-1) * (-1) * count₁₆)));

goal {:named "invariant entry"} (forall ARR_SIZE₂₉: int, array1: [int]int, array2: [int]int, array1₃₀: [int]int, array2₃₁: [int]int, count₃₂: int, count₁₆: int, index1₁₁: int, index2₁₂: int, temp₁₃: int ::
      (  0 < ARR_SIZE₂₉
        && 0 <= count₃₂
        && (forall count₇: int ::
              (  0 <= count₇
                && count₇ < count₃₂
                 ==> count₇ < ARR_SIZE₂₉
                  && array1₃₀[count₇] == 0
                  && array2₃₁[count₇] == 0))
        && (forall count₇: int ::
                  0 <= count₇
                  && count₇ < count₃₂
                ||   array1₃₀[count₇] == array1[count₇]
                  && array2₃₁[count₇] == array2[count₇])
        && temp₁₃ == 0
        && count₁₆ == 200
        && array2₃₁[index2₁₂] == 0
        && array1₃₀[index1₁₁] == 0
        && 0 <= index2₁₂
        && index2₁₂ < ARR_SIZE₂₉
        && 0 <= index1₁₁
        && index1₁₁ < ARR_SIZE₂₉
         ==> count₃₂ < ARR_SIZE₂₉));

goal {:named "invariant entry"} (forall ARR_SIZE₂₉: int, array1: [int]int, array2: [int]int, array1₃₀: [int]int, array2₃₁: [int]int, count₃₂: int, count₁₆: int, index1₁₁: int, index2₁₂: int, temp₁₄: int ::
      (  0 < ARR_SIZE₂₉
        && 0 <= count₃₂
        && (forall count₇: int ::
              (  0 <= count₇
                && count₇ < count₃₂
                 ==> count₇ < ARR_SIZE₂₉
                  && array1₃₀[count₇] == 0
                  && array2₃₁[count₇] == 0))
        && (forall count₇: int ::
                  0 <= count₇
                  && count₇ < count₃₂
                ||   array1₃₀[count₇] == array1[count₇]
                  && array2₃₁[count₇] == array2[count₇])
        && temp₁₄ == 0
        && array2₃₁[index2₁₂] == 0
        && array1₃₀[index1₁₁] == 0
        && 0 <= index2₁₂
        && index2₁₂ < ARR_SIZE₂₉
        && 0 <= index1₁₁
        && index1₁₁ < ARR_SIZE₂₉
         ==> count₃₂ < ARR_SIZE₂₉
          || count₁₆ == 200));

