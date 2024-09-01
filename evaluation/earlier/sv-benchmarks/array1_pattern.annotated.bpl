data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall ARR_SIZE₂₆: int ::
          (true
             ==> true
              && (0 < ARR_SIZE₂₆
                 ==> (forall array1: [int]int ::
                      (forall array2: [int]int ::
                              true
                              && 0 <= 0
                              && 0 <= ARR_SIZE₂₆
                              && (forall x₇: int ::
                                    ((exists count₆: int ::
                                            x₇ == count₆
                                            && 0 <= count₆
                                            && count₆ < 0)
                                       ==> (exists count₆: int ::
                                              count₆ < ARR_SIZE₂₆
                                              && x₇ == count₆
                                              && 0 <= count₆
                                              && count₆ < 0
                                              && array1[x₇] == 0)))
                              && (forall x₇: int ::
                                    (!((exists count₆: int ::
                                            x₇ == count₆
                                            && 0 <= count₆
                                            && count₆ < 0)
                                    )
                                       ==> array1[x₇] == array1[x₇]))
                              && (forall x₈: int ::
                                    ((exists count₆: int ::
                                            x₈ == count₆
                                            && 0 <= count₆
                                            && count₆ < 0)
                                       ==> (exists count₆: int ::
                                              count₆ < ARR_SIZE₂₆
                                              && x₈ == count₆
                                              && 0 <= count₆
                                              && count₆ < 0
                                              && array2[x₈] == 0)))
                              && (forall x₈: int ::
                                    (!((exists count₆: int ::
                                            x₈ == count₆
                                            && 0 <= count₆
                                            && count₆ < 0)
                                    )
                                       ==> array2[x₈] == array2[x₈]))
                              && (forall count₆: int ::
                                    (  count₆ <= count₆
                                      && 0 <= count₆
                                      && count₆ < 0
                                       ==> count₆ < ARR_SIZE₂₆))
                              && (forall array1₂₇: [int]int, array2₂₈: [int]int, count₂₉: int ::
                                    (  true
                                      && 0 <= count₂₉
                                      && count₂₉ <= ARR_SIZE₂₆
                                      && (forall x₇: int ::
                                            ((exists count₆: int ::
                                                    x₇ == count₆
                                                    && 0 <= count₆
                                                    && count₆ < count₂₉)
                                               ==> (exists count₆: int ::
                                                      count₆ < ARR_SIZE₂₆
                                                      && x₇ == count₆
                                                      && 0 <= count₆
                                                      && count₆ < count₂₉
                                                      && array1₂₇[x₇] == 0)))
                                      && (forall x₇: int ::
                                            (!((exists count₆: int ::
                                                    x₇ == count₆
                                                    && 0 <= count₆
                                                    && count₆ < count₂₉)
                                            )
                                               ==> array1₂₇[x₇] == array1[x₇]))
                                      && (forall x₈: int ::
                                            ((exists count₆: int ::
                                                    x₈ == count₆
                                                    && 0 <= count₆
                                                    && count₆ < count₂₉)
                                               ==> (exists count₆: int ::
                                                      count₆ < ARR_SIZE₂₆
                                                      && x₈ == count₆
                                                      && 0 <= count₆
                                                      && count₆ < count₂₉
                                                      && array2₂₈[x₈] == 0)))
                                      && (forall x₈: int ::
                                            (!((exists count₆: int ::
                                                    x₈ == count₆
                                                    && 0 <= count₆
                                                    && count₆ < count₂₉)
                                            )
                                               ==> array2₂₈[x₈] == array2[x₈]))
                                      && (forall count₆: int ::
                                            (  count₆ <= count₆
                                              && 0 <= count₆
                                              && count₆ < count₂₉
                                               ==> count₆ < ARR_SIZE₂₆))
                                       ==> (count₂₉ < ARR_SIZE₂₆
                                           ==> true
                                            && 0 <= count₂₉ + 1
                                            && count₂₉ + 1 <= ARR_SIZE₂₆
                                            && (forall x₇: int ::
                                                  ((exists count₆: int ::
                                                          x₇ == count₆
                                                          && 0 <= count₆
                                                          && count₆ < count₂₉ + 1)
                                                     ==> (exists count₆: int ::
                                                            count₆ < ARR_SIZE₂₆
                                                            && x₇ == count₆
                                                            && 0 <= count₆
                                                            && count₆ < count₂₉ + 1
                                                            && array1₂₇[count₂₉ := 0][x₇] == 0)))
                                            && (forall x₇: int ::
                                                  (!((exists count₆: int ::
                                                          x₇ == count₆
                                                          && 0 <= count₆
                                                          && count₆ < count₂₉ + 1)
                                                  )
                                                     ==> array1₂₇[count₂₉ := 0][x₇] == array1[x₇]))
                                            && (forall x₈: int ::
                                                  ((exists count₆: int ::
                                                          x₈ == count₆
                                                          && 0 <= count₆
                                                          && count₆ < count₂₉ + 1)
                                                     ==> (exists count₆: int ::
                                                            count₆ < ARR_SIZE₂₆
                                                            && x₈ == count₆
                                                            && 0 <= count₆
                                                            && count₆ < count₂₉ + 1
                                                            && array2₂₈[count₂₉ := 0][x₈] == 0)))
                                            && (forall x₈: int ::
                                                  (!((exists count₆: int ::
                                                          x₈ == count₆
                                                          && 0 <= count₆
                                                          && count₆ < count₂₉ + 1)
                                                  )
                                                     ==> array2₂₈[count₂₉ := 0][x₈] == array2[x₈]))
                                            && (forall count₆: int ::
                                                  (  count₆ <= count₆
                                                    && 0 <= count₆
                                                    && count₆ < count₂₉ + 1
                                                     ==> count₆ < ARR_SIZE₂₆))
                                            && true
                                            && (true
                                               ==> true))
                                        && (!(count₂₉ < ARR_SIZE₂₆
                                        )
                                           ==> true
                                            && (true
                                               ==> true
                                                && (forall x₁₆: int ::
                                                      ((exists index₁₂: int ::
                                                            x₁₆ == index₁₂)
                                                         ==> (exists index₁₂: int, temp₁₃: int ::
                                                                temp₁₃ != 0
                                                                && 0 <= index₁₂
                                                                && index₁₂ < ARR_SIZE₂₆
                                                                && x₁₆ == index₁₂
                                                                && array1₂₇[x₁₆] == (-1) * (-1) * index₁₂)))
                                                && (forall x₁₆: int ::
                                                      (!((exists index₁₂: int ::
                                                            x₁₆ == index₁₂)
                                                      )
                                                         ==> array1₂₇[x₁₆] == array1₂₇[x₁₆]))
                                                && (forall x₁₇: int ::
                                                      ((exists index₁₂: int ::
                                                            x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆)
                                                         ==> (exists index₁₂: int, temp₁₃: int ::
                                                                temp₁₃ != 0
                                                                && 0 <= index₁₂
                                                                && index₁₂ < ARR_SIZE₂₆
                                                                && x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆
                                                                && array2₂₈[x₁₇] == (-1) * index₁₂)))
                                                && (forall x₁₇: int ::
                                                      (!((exists index₁₂: int ::
                                                            x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆)
                                                      )
                                                         ==> array2₂₈[x₁₇] == array2₂₈[x₁₇]))
                                                && !((exists index₁₂: int, temp₁₃: int ::
                                                        temp₁₃ == 0
                                                        && 0 <= index₁₂
                                                        && index₁₂ < ARR_SIZE₂₆)
                                                )
                                                && (forall array1₃₁: [int]int, array2₃₂: [int]int ::
                                                      (  true
                                                        && (forall x₁₆: int ::
                                                              ((exists index₁₂: int ::
                                                                    x₁₆ == index₁₂)
                                                                 ==> (exists index₁₂: int, temp₁₃: int ::
                                                                        temp₁₃ != 0
                                                                        && 0 <= index₁₂
                                                                        && index₁₂ < ARR_SIZE₂₆
                                                                        && x₁₆ == index₁₂
                                                                        && array1₃₁[x₁₆] == (-1) * (-1) * index₁₂)))
                                                        && (forall x₁₆: int ::
                                                              (!((exists index₁₂: int ::
                                                                    x₁₆ == index₁₂)
                                                              )
                                                                 ==> array1₃₁[x₁₆] == array1₂₇[x₁₆]))
                                                        && (forall x₁₇: int ::
                                                              ((exists index₁₂: int ::
                                                                    x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆)
                                                                 ==> (exists index₁₂: int, temp₁₃: int ::
                                                                        temp₁₃ != 0
                                                                        && 0 <= index₁₂
                                                                        && index₁₂ < ARR_SIZE₂₆
                                                                        && x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆
                                                                        && array2₃₂[x₁₇] == (-1) * index₁₂)))
                                                        && (forall x₁₇: int ::
                                                              (!((exists index₁₂: int ::
                                                                    x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆)
                                                              )
                                                                 ==> array2₃₂[x₁₇] == array2₂₈[x₁₇]))
                                                        && !((exists index₁₂: int, temp₁₃: int ::
                                                                temp₁₃ == 0
                                                                && 0 <= index₁₂
                                                                && index₁₂ < ARR_SIZE₂₆)
                                                        )
                                                         ==> (1 != 0
                                                             ==> true
                                                              && (forall index₃₈: int ::
                                                                    (true
                                                                       ==> true
                                                                        && (  0 <= index₃₈
                                                                          && index₃₈ < ARR_SIZE₂₆
                                                                           ==> true
                                                                            && (forall temp₃₉: int ::
                                                                                  (true
                                                                                     ==> (temp₃₉ == 0
                                                                                         ==> ((true
                                                                                           ==> true)
                                                                                           ==> true
                                                                                            && 0 <= 0
                                                                                            && 0 <= ARR_SIZE₂₆
                                                                                            && (forall count₂₃: int ::
                                                                                                  (  count₂₃ <= count₂₃
                                                                                                    && 0 <= count₂₃
                                                                                                    && count₂₃ < 0
                                                                                                     ==> count₂₃ < ARR_SIZE₂₆))
                                                                                            && (forall sum₄₀: int, count₄₁: int ::
                                                                                                  (  true
                                                                                                    && 0 <= count₄₁
                                                                                                    && count₄₁ <= ARR_SIZE₂₆
                                                                                                    && (forall count₂₃: int ::
                                                                                                          (  count₂₃ <= count₂₃
                                                                                                            && 0 <= count₂₃
                                                                                                            && count₂₃ < count₄₁
                                                                                                             ==> count₂₃ < ARR_SIZE₂₆))
                                                                                                     ==> (count₄₁ < ARR_SIZE₂₆
                                                                                                         ==> true
                                                                                                          && 0 <= count₄₁ + 1
                                                                                                          && count₄₁ + 1 <= ARR_SIZE₂₆
                                                                                                          && (forall count₂₃: int ::
                                                                                                                (  count₂₃ <= count₂₃
                                                                                                                  && 0 <= count₂₃
                                                                                                                  && count₂₃ < count₄₁ + 1
                                                                                                                   ==> count₂₃ < ARR_SIZE₂₆))
                                                                                                          && true
                                                                                                          && (true
                                                                                                             ==> true))
                                                                                                      && (!(count₄₁ < ARR_SIZE₂₆
                                                                                                      )
                                                                                                         ==> true
                                                                                                          && (true
                                                                                                             ==> sum₄₀ == 0
                                                                                                              && (true
                                                                                                                 ==> true)))))))
                                                                                      && (temp₃₉ != 0
                                                                                         ==> true
                                                                                          && (forall x₁₆: int ::
                                                                                                ((exists index₁₂: int ::
                                                                                                      x₁₆ == index₁₂)
                                                                                                   ==> (exists index₁₂: int, temp₁₃: int ::
                                                                                                          temp₁₃ != 0
                                                                                                          && 0 <= index₁₂
                                                                                                          && index₁₂ < ARR_SIZE₂₆
                                                                                                          && x₁₆ == index₁₂
                                                                                                          && array1₃₁[index₃₈ := (-1) * (-1) * index₃₈][x₁₆] == (-1) * (-1) * index₁₂)))
                                                                                          && (forall x₁₆: int ::
                                                                                                (!((exists index₁₂: int ::
                                                                                                      x₁₆ == index₁₂)
                                                                                                )
                                                                                                   ==> array1₃₁[index₃₈ := (-1) * (-1) * index₃₈][x₁₆] == array1₂₇[x₁₆]))
                                                                                          && (forall x₁₇: int ::
                                                                                                ((exists index₁₂: int ::
                                                                                                      x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆)
                                                                                                   ==> (exists index₁₂: int, temp₁₃: int ::
                                                                                                          temp₁₃ != 0
                                                                                                          && 0 <= index₁₂
                                                                                                          && index₁₂ < ARR_SIZE₂₆
                                                                                                          && x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆
                                                                                                          && array2₃₂[ARR_SIZE₂₆ - 1 - index₃₈ := (-1) * index₃₈][x₁₇] == (-1) * index₁₂)))
                                                                                          && (forall x₁₇: int ::
                                                                                                (!((exists index₁₂: int ::
                                                                                                      x₁₇ == -1 + -index₁₂ + ARR_SIZE₂₆)
                                                                                                )
                                                                                                   ==> array2₃₂[ARR_SIZE₂₆ - 1 - index₃₈ := (-1) * index₃₈][x₁₇] == array2₂₈[x₁₇]))
                                                                                          && !((exists index₁₂: int, temp₁₃: int ::
                                                                                                  temp₁₃ == 0
                                                                                                  && 0 <= index₁₂
                                                                                                  && index₁₂ < ARR_SIZE₂₆)
                                                                                          )
                                                                                          && true
                                                                                          && (true
                                                                                             ==> true))))))))
                                                          && (!(1 != 0
                                                          )
                                                             ==> true
                                                              && (true
                                                                 ==> true
                                                                  && 0 <= 0
                                                                  && 0 <= ARR_SIZE₂₆
                                                                  && (forall count₂₃: int ::
                                                                        (  count₂₃ <= count₂₃
                                                                          && 0 <= count₂₃
                                                                          && count₂₃ < 0
                                                                           ==> count₂₃ < ARR_SIZE₂₆))
                                                                  && (forall sum₃₄: int, count₃₅: int ::
                                                                        (  true
                                                                          && 0 <= count₃₅
                                                                          && count₃₅ <= ARR_SIZE₂₆
                                                                          && (forall count₂₃: int ::
                                                                                (  count₂₃ <= count₂₃
                                                                                  && 0 <= count₂₃
                                                                                  && count₂₃ < count₃₅
                                                                                   ==> count₂₃ < ARR_SIZE₂₆))
                                                                           ==> (count₃₅ < ARR_SIZE₂₆
                                                                               ==> true
                                                                                && 0 <= count₃₅ + 1
                                                                                && count₃₅ + 1 <= ARR_SIZE₂₆
                                                                                && (forall count₂₃: int ::
                                                                                      (  count₂₃ <= count₂₃
                                                                                        && 0 <= count₂₃
                                                                                        && count₂₃ < count₃₅ + 1
                                                                                         ==> count₂₃ < ARR_SIZE₂₆))
                                                                                && true
                                                                                && (true
                                                                                   ==> true))
                                                                            && (!(count₃₅ < ARR_SIZE₂₆
                                                                            )
                                                                               ==> true
                                                                                && (true
                                                                                   ==> sum₃₄ == 0
                                                                                    && (true
                                                                                       ==> true)))))))))))))))))));

