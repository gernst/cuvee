data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall ARR_SIZE₂₆: int ::
      (forall array1: [int]int, array2: [int]int ::
            (0 < ARR_SIZE₂₆
               ==> 0 <= 0
                && 0 <= ARR_SIZE₂₆
                && (forall x₇: int, count₆: int ::
                      (  x₇ == count₆
                        && 0 <= count₆
                        && count₆ < 0
                         ==> (exists count₆: int ::
                                count₆ < ARR_SIZE₂₆
                                && x₇ == count₆
                                && 0 <= count₆
                                && count₆ < 0
                                && array1[x₇] == 0)))
                && (forall x₇: int ::
                        (exists count₆: int ::
                                x₇ == count₆
                                && 0 <= count₆
                                && count₆ < 0)
                        || array1[x₇] == array1[x₇])
                && (forall x₈: int, count₆: int ::
                      (  x₈ == count₆
                        && 0 <= count₆
                        && count₆ < 0
                         ==> (exists count₆: int ::
                                count₆ < ARR_SIZE₂₆
                                && x₈ == count₆
                                && 0 <= count₆
                                && count₆ < 0
                                && array2[x₈] == 0)))
                && (forall x₈: int ::
                        (exists count₆: int ::
                                x₈ == count₆
                                && 0 <= count₆
                                && count₆ < 0)
                        || array2[x₈] == array2[x₈])
                && (forall count₆: int ::
                      (  0 <= count₆
                        && count₆ < 0
                         ==> count₆ < ARR_SIZE₂₆))
                && (forall array1₂₇: [int]int, array2₂₈: [int]int, count₂₉: int ::
                      (  0 <= count₂₉
                        && count₂₉ <= ARR_SIZE₂₆
                        && (forall x₇: int, count₆: int ::
                              (  x₇ == count₆
                                && 0 <= count₆
                                && count₆ < count₂₉
                                 ==> (exists count₆: int ::
                                        count₆ < ARR_SIZE₂₆
                                        && x₇ == count₆
                                        && 0 <= count₆
                                        && count₆ < count₂₉
                                        && array1₂₇[x₇] == 0)))
                        && (forall x₇: int ::
                                (exists count₆: int ::
                                        x₇ == count₆
                                        && 0 <= count₆
                                        && count₆ < count₂₉)
                                || array1₂₇[x₇] == array1[x₇])
                        && (forall x₈: int, count₆: int ::
                              (  x₈ == count₆
                                && 0 <= count₆
                                && count₆ < count₂₉
                                 ==> (exists count₆: int ::
                                        count₆ < ARR_SIZE₂₆
                                        && x₈ == count₆
                                        && 0 <= count₆
                                        && count₆ < count₂₉
                                        && array2₂₈[x₈] == 0)))
                        && (forall x₈: int ::
                                (exists count₆: int ::
                                        x₈ == count₆
                                        && 0 <= count₆
                                        && count₆ < count₂₉)
                                || array2₂₈[x₈] == array2[x₈])
                        && (forall count₆: int ::
                              (  0 <= count₆
                                && count₆ < count₂₉
                                 ==> count₆ < ARR_SIZE₂₆))
                         ==> (count₂₉ < ARR_SIZE₂₆
                             ==> 0 <= count₂₉ + 1
                              && count₂₉ + 1 <= ARR_SIZE₂₆
                              && (forall x₇: int, count₆: int ::
                                    (  x₇ == count₆
                                      && 0 <= count₆
                                      && count₆ < count₂₉ + 1
                                       ==> (exists count₆: int ::
                                              count₆ < ARR_SIZE₂₆
                                              && x₇ == count₆
                                              && 0 <= count₆
                                              && count₆ < count₂₉ + 1
                                              && array1₂₇[count₂₉ := 0][x₇] == 0)))
                              && (forall x₇: int ::
                                      (exists count₆: int ::
                                              x₇ == count₆
                                              && 0 <= count₆
                                              && count₆ < count₂₉ + 1)
                                      || array1₂₇[count₂₉ := 0][x₇] == array1[x₇])
                              && (forall x₈: int, count₆: int ::
                                    (  x₈ == count₆
                                      && 0 <= count₆
                                      && count₆ < count₂₉ + 1
                                       ==> (exists count₆: int ::
                                              count₆ < ARR_SIZE₂₆
                                              && x₈ == count₆
                                              && 0 <= count₆
                                              && count₆ < count₂₉ + 1
                                              && array2₂₈[count₂₉ := 0][x₈] == 0)))
                              && (forall x₈: int ::
                                      (exists count₆: int ::
                                              x₈ == count₆
                                              && 0 <= count₆
                                              && count₆ < count₂₉ + 1)
                                      || array2₂₈[count₂₉ := 0][x₈] == array2[x₈])
                              && (forall count₆: int ::
                                    (  0 <= count₆
                                      && count₆ < count₂₉ + 1
                                       ==> count₆ < ARR_SIZE₂₆)))
                          &&   count₂₉ < ARR_SIZE₂₆
                            ||   (forall x₁₆: int, index₁₂: int ::
                                    (x₁₆ == index₁₂
                                       ==> (exists temp₁₃: int ::
                                            (temp₁₃ == 0
                                               ==> false))))
                              && (forall x₁₆: int ::
                                      (exists index₁₂: int ::
                                            x₁₆ == index₁₂)
                                      || array1₂₇[x₁₆] == array1₂₇[x₁₆])
                              && (forall x₁₇: int, index₁₂: int ::
                                    (x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆
                                       ==> (exists temp₁₃: int ::
                                            (temp₁₃ == 0
                                               ==> false))))
                              && (forall x₁₇: int ::
                                      (exists index₁₂: int ::
                                            x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆)
                                      || array2₂₈[x₁₇] == array2₂₈[x₁₇])
                              && (forall index₁₂: int, temp₁₃: int ::
                                    (  temp₁₃ == 0
                                      && 0 <= index₁₂
                                      && index₁₂ < ARR_SIZE₂₆
                                       ==> false)))))));

