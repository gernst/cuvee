data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall ARR_SIZE₃₃: int, array1: [int]int, array2: [int]int, array1₃₄: [int]int, array2₃₅: [int]int, count₃₆: int, count₁₈: int, index1₁₃: int, index2₁₄: int, temp₁₅: int ::
      (  0 < ARR_SIZE₃₃
        && 0 <= count₃₆
        && count₃₆ <= ARR_SIZE₃₃
        && (forall x₈: int, count₇: int ::
              (  x₈ == count₇
                && 0 <= count₇
                && count₇ < count₃₆
                 ==> (exists count₇: int ::
                        count₇ < ARR_SIZE₃₃
                        && x₈ == count₇
                        && 0 <= count₇
                        && count₇ < count₃₆
                        && array1₃₄[x₈] == 0)))
        && (forall x₈: int ::
                (exists count₇: int ::
                        x₈ == count₇
                        && 0 <= count₇
                        && count₇ < count₃₆)
                || array1₃₄[x₈] == array1[x₈])
        && (forall x₉: int, count₇: int ::
              (  x₉ == count₇
                && 0 <= count₇
                && count₇ < count₃₆
                 ==> (exists count₇: int ::
                        count₇ < ARR_SIZE₃₃
                        && x₉ == count₇
                        && 0 <= count₇
                        && count₇ < count₃₆
                        && array2₃₅[x₉] == 0)))
        && (forall x₉: int ::
                (exists count₇: int ::
                        x₉ == count₇
                        && 0 <= count₇
                        && count₇ < count₃₆)
                || array2₃₅[x₉] == array2[x₉])
        && (forall count₇: int ::
              (  0 <= count₇
                && count₇ < count₃₆
                 ==> count₇ < ARR_SIZE₃₃))
        && temp₁₅ == 0
        && count₁₈ == 200
        && array2₃₅[index2₁₄] == 0
        && array1₃₄[index1₁₃] == 0
        && 0 <= index2₁₄
        && index2₁₄ < ARR_SIZE₃₃
        && 0 <= index1₁₃
        && index1₁₃ < ARR_SIZE₃₃
         ==> count₃₆ < ARR_SIZE₃₃));

goal (forall ARR_SIZE₃₃: int, array1: [int]int, array2: [int]int, array1₃₄: [int]int, array2₃₅: [int]int, count₃₆: int, count₁₈: int, index1₁₃: int, index2₁₄: int, temp₁₆: int ::
      (  0 < ARR_SIZE₃₃
        && 0 <= count₃₆
        && count₃₆ <= ARR_SIZE₃₃
        && (forall x₈: int, count₇: int ::
              (  x₈ == count₇
                && 0 <= count₇
                && count₇ < count₃₆
                 ==> (exists count₇: int ::
                        count₇ < ARR_SIZE₃₃
                        && x₈ == count₇
                        && 0 <= count₇
                        && count₇ < count₃₆
                        && array1₃₄[x₈] == 0)))
        && (forall x₈: int ::
                (exists count₇: int ::
                        x₈ == count₇
                        && 0 <= count₇
                        && count₇ < count₃₆)
                || array1₃₄[x₈] == array1[x₈])
        && (forall x₉: int, count₇: int ::
              (  x₉ == count₇
                && 0 <= count₇
                && count₇ < count₃₆
                 ==> (exists count₇: int ::
                        count₇ < ARR_SIZE₃₃
                        && x₉ == count₇
                        && 0 <= count₇
                        && count₇ < count₃₆
                        && array2₃₅[x₉] == 0)))
        && (forall x₉: int ::
                (exists count₇: int ::
                        x₉ == count₇
                        && 0 <= count₇
                        && count₇ < count₃₆)
                || array2₃₅[x₉] == array2[x₉])
        && (forall count₇: int ::
              (  0 <= count₇
                && count₇ < count₃₆
                 ==> count₇ < ARR_SIZE₃₃))
        && temp₁₆ == 0
        && array2₃₅[index2₁₄] == 0
        && array1₃₄[index1₁₃] == 0
        && 0 <= index2₁₄
        && index2₁₄ < ARR_SIZE₃₃
        && 0 <= index1₁₃
        && index1₁₃ < ARR_SIZE₃₃
         ==> count₁₈ == 200
          || count₃₆ < ARR_SIZE₃₃));

