data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall ARR_SIZE₃₃: int ::
          (true
             ==> true
              && (0 < ARR_SIZE₃₃
                 ==> (forall array1: [int]int ::
                      (forall array2: [int]int ::
                              true
                              && 0 <= 0
                              && 0 <= ARR_SIZE₃₃
                              && (forall x₈: int ::
                                    ((exists count₇: int ::
                                            x₈ == count₇
                                            && 0 <= count₇
                                            && count₇ < 0)
                                       ==> (exists count₇: int ::
                                              count₇ < ARR_SIZE₃₃
                                              && x₈ == count₇
                                              && 0 <= count₇
                                              && count₇ < 0
                                              && array1[x₈] == 0)))
                              && (forall x₈: int ::
                                    (!((exists count₇: int ::
                                            x₈ == count₇
                                            && 0 <= count₇
                                            && count₇ < 0)
                                    )
                                       ==> array1[x₈] == array1[x₈]))
                              && (forall x₉: int ::
                                    ((exists count₇: int ::
                                            x₉ == count₇
                                            && 0 <= count₇
                                            && count₇ < 0)
                                       ==> (exists count₇: int ::
                                              count₇ < ARR_SIZE₃₃
                                              && x₉ == count₇
                                              && 0 <= count₇
                                              && count₇ < 0
                                              && array2[x₉] == 0)))
                              && (forall x₉: int ::
                                    (!((exists count₇: int ::
                                            x₉ == count₇
                                            && 0 <= count₇
                                            && count₇ < 0)
                                    )
                                       ==> array2[x₉] == array2[x₉]))
                              && (forall count₇: int ::
                                    (  count₇ <= count₇
                                      && 0 <= count₇
                                      && count₇ < 0
                                       ==> count₇ < ARR_SIZE₃₃))
                              && (forall array1₃₄: [int]int, array2₃₅: [int]int, count₃₆: int ::
                                    (  true
                                      && 0 <= count₃₆
                                      && count₃₆ <= ARR_SIZE₃₃
                                      && (forall x₈: int ::
                                            ((exists count₇: int ::
                                                    x₈ == count₇
                                                    && 0 <= count₇
                                                    && count₇ < count₃₆)
                                               ==> (exists count₇: int ::
                                                      count₇ < ARR_SIZE₃₃
                                                      && x₈ == count₇
                                                      && 0 <= count₇
                                                      && count₇ < count₃₆
                                                      && array1₃₄[x₈] == 0)))
                                      && (forall x₈: int ::
                                            (!((exists count₇: int ::
                                                    x₈ == count₇
                                                    && 0 <= count₇
                                                    && count₇ < count₃₆)
                                            )
                                               ==> array1₃₄[x₈] == array1[x₈]))
                                      && (forall x₉: int ::
                                            ((exists count₇: int ::
                                                    x₉ == count₇
                                                    && 0 <= count₇
                                                    && count₇ < count₃₆)
                                               ==> (exists count₇: int ::
                                                      count₇ < ARR_SIZE₃₃
                                                      && x₉ == count₇
                                                      && 0 <= count₇
                                                      && count₇ < count₃₆
                                                      && array2₃₅[x₉] == 0)))
                                      && (forall x₉: int ::
                                            (!((exists count₇: int ::
                                                    x₉ == count₇
                                                    && 0 <= count₇
                                                    && count₇ < count₃₆)
                                            )
                                               ==> array2₃₅[x₉] == array2[x₉]))
                                      && (forall count₇: int ::
                                            (  count₇ <= count₇
                                              && 0 <= count₇
                                              && count₇ < count₃₆
                                               ==> count₇ < ARR_SIZE₃₃))
                                       ==> (count₃₆ < ARR_SIZE₃₃
                                           ==> true
                                            && 0 <= count₃₆ + 1
                                            && count₃₆ + 1 <= ARR_SIZE₃₃
                                            && (forall x₈: int ::
                                                  ((exists count₇: int ::
                                                          x₈ == count₇
                                                          && 0 <= count₇
                                                          && count₇ < count₃₆ + 1)
                                                     ==> (exists count₇: int ::
                                                            count₇ < ARR_SIZE₃₃
                                                            && x₈ == count₇
                                                            && 0 <= count₇
                                                            && count₇ < count₃₆ + 1
                                                            && array1₃₄[count₃₆ := 0][x₈] == 0)))
                                            && (forall x₈: int ::
                                                  (!((exists count₇: int ::
                                                          x₈ == count₇
                                                          && 0 <= count₇
                                                          && count₇ < count₃₆ + 1)
                                                  )
                                                     ==> array1₃₄[count₃₆ := 0][x₈] == array1[x₈]))
                                            && (forall x₉: int ::
                                                  ((exists count₇: int ::
                                                          x₉ == count₇
                                                          && 0 <= count₇
                                                          && count₇ < count₃₆ + 1)
                                                     ==> (exists count₇: int ::
                                                            count₇ < ARR_SIZE₃₃
                                                            && x₉ == count₇
                                                            && 0 <= count₇
                                                            && count₇ < count₃₆ + 1
                                                            && array2₃₅[count₃₆ := 0][x₉] == 0)))
                                            && (forall x₉: int ::
                                                  (!((exists count₇: int ::
                                                          x₉ == count₇
                                                          && 0 <= count₇
                                                          && count₇ < count₃₆ + 1)
                                                  )
                                                     ==> array2₃₅[count₃₆ := 0][x₉] == array2[x₉]))
                                            && (forall count₇: int ::
                                                  (  count₇ <= count₇
                                                    && 0 <= count₇
                                                    && count₇ < count₃₆ + 1
                                                     ==> count₇ < ARR_SIZE₃₃))
                                            && true
                                            && (true
                                               ==> true))
                                        && (!(count₃₆ < ARR_SIZE₃₃
                                        )
                                           ==> true
                                            && (true
                                               ==> true
                                                && (forall x₂₁: int ::
                                                      ((exists index2₁₄: int ::
                                                            x₂₁ == index2₁₄)
                                                         ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                                                                  temp₁₅ != 0
                                                                  && count₁₈ == 200
                                                                  && array2₃₅[index2₁₄] == 0
                                                                  && array1₃₄[index1₁₃] == 0
                                                                  && 0 <= index2₁₄
                                                                  && index2₁₄ < ARR_SIZE₃₃
                                                                  && 0 <= index1₁₃
                                                                  && index1₁₃ < ARR_SIZE₃₃
                                                                  && x₂₁ == index2₁₄
                                                                  && array2₃₅[x₂₁] == (-1) * count₁₈)
                                                          || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                                                                  temp₁₆ != 0
                                                                  && count₁₈ != 200
                                                                  && array2₃₅[index2₁₄] == 0
                                                                  && array1₃₄[index1₁₃] == 0
                                                                  && 0 <= index2₁₄
                                                                  && index2₁₄ < ARR_SIZE₃₃
                                                                  && 0 <= index1₁₃
                                                                  && index1₁₃ < ARR_SIZE₃₃
                                                                  && x₂₁ == index2₁₄
                                                                  && array2₃₅[x₂₁] == (-1) * count₁₈)))
                                                && (forall x₂₁: int ::
                                                      (!((exists index2₁₄: int ::
                                                            x₂₁ == index2₁₄)
                                                      )
                                                         ==> array2₃₅[x₂₁] == array2₃₅[x₂₁]))
                                                && (forall x₂₂: int ::
                                                      ((exists index1₁₃: int ::
                                                            x₂₂ == index1₁₃)
                                                         ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                                                                  temp₁₅ != 0
                                                                  && count₁₈ == 200
                                                                  && array2₃₅[index2₁₄] == 0
                                                                  && array1₃₄[index1₁₃] == 0
                                                                  && 0 <= index2₁₄
                                                                  && index2₁₄ < ARR_SIZE₃₃
                                                                  && 0 <= index1₁₃
                                                                  && index1₁₃ < ARR_SIZE₃₃
                                                                  && x₂₂ == index1₁₃
                                                                  && array1₃₄[x₂₂] == (-1) * (-1) * count₁₈)
                                                          || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                                                                  temp₁₆ != 0
                                                                  && count₁₈ != 200
                                                                  && array2₃₅[index2₁₄] == 0
                                                                  && array1₃₄[index1₁₃] == 0
                                                                  && 0 <= index2₁₄
                                                                  && index2₁₄ < ARR_SIZE₃₃
                                                                  && 0 <= index1₁₃
                                                                  && index1₁₃ < ARR_SIZE₃₃
                                                                  && x₂₂ == index1₁₃
                                                                  && array1₃₄[x₂₂] == (-1) * (-1) * count₁₈)))
                                                && (forall x₂₂: int ::
                                                      (!((exists index1₁₃: int ::
                                                            x₂₂ == index1₁₃)
                                                      )
                                                         ==> array1₃₄[x₂₂] == array1₃₄[x₂₂]))
                                                && (forall count₁₈: int ::
                                                        !((exists index1₁₃: int, index2₁₄: int, temp₁₅: int ::
                                                                temp₁₅ == 0
                                                                && count₁₈ == 200
                                                                && array2₃₅[index2₁₄] == 0
                                                                && array1₃₄[index1₁₃] == 0
                                                                && 0 <= index2₁₄
                                                                && index2₁₄ < ARR_SIZE₃₃
                                                                && 0 <= index1₁₃
                                                                && index1₁₃ < ARR_SIZE₃₃)
                                                        )
                                                        && !((exists index1₁₃: int, index2₁₄: int, temp₁₆: int ::
                                                                temp₁₆ == 0
                                                                && count₁₈ != 200
                                                                && array2₃₅[index2₁₄] == 0
                                                                && array1₃₄[index1₁₃] == 0
                                                                && 0 <= index2₁₄
                                                                && index2₁₄ < ARR_SIZE₃₃
                                                                && 0 <= index1₁₃
                                                                && index1₁₃ < ARR_SIZE₃₃)
                                                        ))
                                                && (forall array2₃₇: [int]int, count₃₉: int, array1₄₁: [int]int ::
                                                      (  true
                                                        && (forall x₂₁: int ::
                                                              ((exists index2₁₄: int ::
                                                                    x₂₁ == index2₁₄)
                                                                 ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                                                                          temp₁₅ != 0
                                                                          && count₁₈ == 200
                                                                          && array2₃₇[index2₁₄] == 0
                                                                          && array1₄₁[index1₁₃] == 0
                                                                          && 0 <= index2₁₄
                                                                          && index2₁₄ < ARR_SIZE₃₃
                                                                          && 0 <= index1₁₃
                                                                          && index1₁₃ < ARR_SIZE₃₃
                                                                          && x₂₁ == index2₁₄
                                                                          && array2₃₇[x₂₁] == (-1) * count₁₈)
                                                                  || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                                                                          temp₁₆ != 0
                                                                          && count₁₈ != 200
                                                                          && array2₃₇[index2₁₄] == 0
                                                                          && array1₄₁[index1₁₃] == 0
                                                                          && 0 <= index2₁₄
                                                                          && index2₁₄ < ARR_SIZE₃₃
                                                                          && 0 <= index1₁₃
                                                                          && index1₁₃ < ARR_SIZE₃₃
                                                                          && x₂₁ == index2₁₄
                                                                          && array2₃₇[x₂₁] == (-1) * count₁₈)))
                                                        && (forall x₂₁: int ::
                                                              (!((exists index2₁₄: int ::
                                                                    x₂₁ == index2₁₄)
                                                              )
                                                                 ==> array2₃₇[x₂₁] == array2₃₅[x₂₁]))
                                                        && (forall x₂₂: int ::
                                                              ((exists index1₁₃: int ::
                                                                    x₂₂ == index1₁₃)
                                                                 ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                                                                          temp₁₅ != 0
                                                                          && count₁₈ == 200
                                                                          && array2₃₇[index2₁₄] == 0
                                                                          && array1₄₁[index1₁₃] == 0
                                                                          && 0 <= index2₁₄
                                                                          && index2₁₄ < ARR_SIZE₃₃
                                                                          && 0 <= index1₁₃
                                                                          && index1₁₃ < ARR_SIZE₃₃
                                                                          && x₂₂ == index1₁₃
                                                                          && array1₄₁[x₂₂] == (-1) * (-1) * count₁₈)
                                                                  || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                                                                          temp₁₆ != 0
                                                                          && count₁₈ != 200
                                                                          && array2₃₇[index2₁₄] == 0
                                                                          && array1₄₁[index1₁₃] == 0
                                                                          && 0 <= index2₁₄
                                                                          && index2₁₄ < ARR_SIZE₃₃
                                                                          && 0 <= index1₁₃
                                                                          && index1₁₃ < ARR_SIZE₃₃
                                                                          && x₂₂ == index1₁₃
                                                                          && array1₄₁[x₂₂] == (-1) * (-1) * count₁₈)))
                                                        && (forall x₂₂: int ::
                                                              (!((exists index1₁₃: int ::
                                                                    x₂₂ == index1₁₃)
                                                              )
                                                                 ==> array1₄₁[x₂₂] == array1₃₄[x₂₂]))
                                                        && (forall count₁₈: int ::
                                                                !((exists index1₁₃: int, index2₁₄: int, temp₁₅: int ::
                                                                        temp₁₅ == 0
                                                                        && count₁₈ == 200
                                                                        && array2₃₇[index2₁₄] == 0
                                                                        && array1₄₁[index1₁₃] == 0
                                                                        && 0 <= index2₁₄
                                                                        && index2₁₄ < ARR_SIZE₃₃
                                                                        && 0 <= index1₁₃
                                                                        && index1₁₃ < ARR_SIZE₃₃)
                                                                )
                                                                && !((exists index1₁₃: int, index2₁₄: int, temp₁₆: int ::
                                                                        temp₁₆ == 0
                                                                        && count₁₈ != 200
                                                                        && array2₃₇[index2₁₄] == 0
                                                                        && array1₄₁[index1₁₃] == 0
                                                                        && 0 <= index2₁₄
                                                                        && index2₁₄ < ARR_SIZE₃₃
                                                                        && 0 <= index1₁₃
                                                                        && index1₁₃ < ARR_SIZE₃₃)
                                                                ))
                                                         ==> (1 != 0
                                                             ==> true
                                                              && (forall index1₄₇: int ::
                                                                    (true
                                                                       ==> true
                                                                        && (forall index2₄₈: int ::
                                                                              (true
                                                                                 ==> true
                                                                                  && (  0 <= index1₄₇
                                                                                    && index1₄₇ < ARR_SIZE₃₃
                                                                                     ==> true
                                                                                      && (  0 <= index2₄₈
                                                                                        && index2₄₈ < ARR_SIZE₃₃
                                                                                         ==> true
                                                                                          && (array1₄₁[index1₄₇] == 0
                                                                                             ==> true
                                                                                              && (array2₃₇[index2₄₈] == 0
                                                                                                 ==> (count₃₉ == 200
                                                                                                     ==> true
                                                                                                      && (forall temp₄₉: int ::
                                                                                                            (true
                                                                                                               ==> (temp₄₉ == 0
                                                                                                                   ==> ((true
                                                                                                                     ==> true)
                                                                                                                     ==> true
                                                                                                                      && 0 <= 0
                                                                                                                      && 0 <= ARR_SIZE₃₃
                                                                                                                      && (forall count₃₀: int ::
                                                                                                                            (  count₃₀ <= count₃₀
                                                                                                                              && 0 <= count₃₀
                                                                                                                              && count₃₀ < 0
                                                                                                                               ==> count₃₀ < ARR_SIZE₃₃))
                                                                                                                      && (forall sum₅₀: int, count₅₁: int ::
                                                                                                                            (  true
                                                                                                                              && 0 <= count₅₁
                                                                                                                              && count₅₁ <= ARR_SIZE₃₃
                                                                                                                              && (forall count₃₀: int ::
                                                                                                                                    (  count₃₀ <= count₃₀
                                                                                                                                      && 0 <= count₃₀
                                                                                                                                      && count₃₀ < count₅₁
                                                                                                                                       ==> count₃₀ < ARR_SIZE₃₃))
                                                                                                                               ==> (count₅₁ < ARR_SIZE₃₃
                                                                                                                                   ==> true
                                                                                                                                    && 0 <= count₅₁ + 1
                                                                                                                                    && count₅₁ + 1 <= ARR_SIZE₃₃
                                                                                                                                    && (forall count₃₀: int ::
                                                                                                                                          (  count₃₀ <= count₃₀
                                                                                                                                            && 0 <= count₃₀
                                                                                                                                            && count₃₀ < count₅₁ + 1
                                                                                                                                             ==> count₃₀ < ARR_SIZE₃₃))
                                                                                                                                    && true
                                                                                                                                    && (true
                                                                                                                                       ==> true))
                                                                                                                                && (!(count₅₁ < ARR_SIZE₃₃
                                                                                                                                )
                                                                                                                                   ==> true
                                                                                                                                    && (true
                                                                                                                                       ==> sum₅₀ == 0
                                                                                                                                        && (true
                                                                                                                                           ==> true)))))))
                                                                                                                && (temp₄₉ != 0
                                                                                                                   ==> true
                                                                                                                    && (forall x₂₁: int ::
                                                                                                                          ((exists index2₁₄: int ::
                                                                                                                                x₂₁ == index2₁₄)
                                                                                                                             ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                                                                                                                                      temp₁₅ != 0
                                                                                                                                      && count₁₈ == 200
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                      && 0 <= index2₁₄
                                                                                                                                      && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                      && 0 <= index1₁₃
                                                                                                                                      && index1₁₃ < ARR_SIZE₃₃
                                                                                                                                      && x₂₁ == index2₁₄
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][x₂₁] == (-1) * count₁₈)
                                                                                                                              || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                                                                                                                                      temp₁₆ != 0
                                                                                                                                      && count₁₈ != 200
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                      && 0 <= index2₁₄
                                                                                                                                      && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                      && 0 <= index1₁₃
                                                                                                                                      && index1₁₃ < ARR_SIZE₃₃
                                                                                                                                      && x₂₁ == index2₁₄
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][x₂₁] == (-1) * count₁₈)))
                                                                                                                    && (forall x₂₁: int ::
                                                                                                                          (!((exists index2₁₄: int ::
                                                                                                                                x₂₁ == index2₁₄)
                                                                                                                          )
                                                                                                                             ==> array2₃₇[index2₄₈ := (-1) * count₃₉][x₂₁] == array2₃₅[x₂₁]))
                                                                                                                    && (forall x₂₂: int ::
                                                                                                                          ((exists index1₁₃: int ::
                                                                                                                                x₂₂ == index1₁₃)
                                                                                                                             ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                                                                                                                                      temp₁₅ != 0
                                                                                                                                      && count₁₈ == 200
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                      && 0 <= index2₁₄
                                                                                                                                      && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                      && 0 <= index1₁₃
                                                                                                                                      && index1₁₃ < ARR_SIZE₃₃
                                                                                                                                      && x₂₂ == index1₁₃
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][x₂₂] == (-1) * (-1) * count₁₈)
                                                                                                                              || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                                                                                                                                      temp₁₆ != 0
                                                                                                                                      && count₁₈ != 200
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                      && 0 <= index2₁₄
                                                                                                                                      && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                      && 0 <= index1₁₃
                                                                                                                                      && index1₁₃ < ARR_SIZE₃₃
                                                                                                                                      && x₂₂ == index1₁₃
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][x₂₂] == (-1) * (-1) * count₁₈)))
                                                                                                                    && (forall x₂₂: int ::
                                                                                                                          (!((exists index1₁₃: int ::
                                                                                                                                x₂₂ == index1₁₃)
                                                                                                                          )
                                                                                                                             ==> array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][x₂₂] == array1₃₄[x₂₂]))
                                                                                                                    && (forall count₁₈: int ::
                                                                                                                            !((exists index1₁₃: int, index2₁₄: int, temp₁₅: int ::
                                                                                                                                    temp₁₅ == 0
                                                                                                                                    && count₁₈ == 200
                                                                                                                                    && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                    && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                    && 0 <= index2₁₄
                                                                                                                                    && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                    && 0 <= index1₁₃
                                                                                                                                    && index1₁₃ < ARR_SIZE₃₃)
                                                                                                                            )
                                                                                                                            && !((exists index1₁₃: int, index2₁₄: int, temp₁₆: int ::
                                                                                                                                    temp₁₆ == 0
                                                                                                                                    && count₁₈ != 200
                                                                                                                                    && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                    && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                    && 0 <= index2₁₄
                                                                                                                                    && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                    && 0 <= index1₁₃
                                                                                                                                    && index1₁₃ < ARR_SIZE₃₃)
                                                                                                                            ))
                                                                                                                    && true
                                                                                                                    && (true
                                                                                                                       ==> true)))))
                                                                                                  && (count₃₉ != 200
                                                                                                     ==> true
                                                                                                      && (forall temp₆₀: int ::
                                                                                                            (true
                                                                                                               ==> (temp₆₀ == 0
                                                                                                                   ==> ((true
                                                                                                                     ==> true)
                                                                                                                     ==> true
                                                                                                                      && 0 <= 0
                                                                                                                      && 0 <= ARR_SIZE₃₃
                                                                                                                      && (forall count₃₀: int ::
                                                                                                                            (  count₃₀ <= count₃₀
                                                                                                                              && 0 <= count₃₀
                                                                                                                              && count₃₀ < 0
                                                                                                                               ==> count₃₀ < ARR_SIZE₃₃))
                                                                                                                      && (forall sum₆₁: int, count₆₂: int ::
                                                                                                                            (  true
                                                                                                                              && 0 <= count₆₂
                                                                                                                              && count₆₂ <= ARR_SIZE₃₃
                                                                                                                              && (forall count₃₀: int ::
                                                                                                                                    (  count₃₀ <= count₃₀
                                                                                                                                      && 0 <= count₃₀
                                                                                                                                      && count₃₀ < count₆₂
                                                                                                                                       ==> count₃₀ < ARR_SIZE₃₃))
                                                                                                                               ==> (count₆₂ < ARR_SIZE₃₃
                                                                                                                                   ==> true
                                                                                                                                    && 0 <= count₆₂ + 1
                                                                                                                                    && count₆₂ + 1 <= ARR_SIZE₃₃
                                                                                                                                    && (forall count₃₀: int ::
                                                                                                                                          (  count₃₀ <= count₃₀
                                                                                                                                            && 0 <= count₃₀
                                                                                                                                            && count₃₀ < count₆₂ + 1
                                                                                                                                             ==> count₃₀ < ARR_SIZE₃₃))
                                                                                                                                    && true
                                                                                                                                    && (true
                                                                                                                                       ==> true))
                                                                                                                                && (!(count₆₂ < ARR_SIZE₃₃
                                                                                                                                )
                                                                                                                                   ==> true
                                                                                                                                    && (true
                                                                                                                                       ==> sum₆₁ == 0
                                                                                                                                        && (true
                                                                                                                                           ==> true)))))))
                                                                                                                && (temp₆₀ != 0
                                                                                                                   ==> true
                                                                                                                    && (forall x₂₁: int ::
                                                                                                                          ((exists index2₁₄: int ::
                                                                                                                                x₂₁ == index2₁₄)
                                                                                                                             ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                                                                                                                                      temp₁₅ != 0
                                                                                                                                      && count₁₈ == 200
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                      && 0 <= index2₁₄
                                                                                                                                      && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                      && 0 <= index1₁₃
                                                                                                                                      && index1₁₃ < ARR_SIZE₃₃
                                                                                                                                      && x₂₁ == index2₁₄
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][x₂₁] == (-1) * count₁₈)
                                                                                                                              || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                                                                                                                                      temp₁₆ != 0
                                                                                                                                      && count₁₈ != 200
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                      && 0 <= index2₁₄
                                                                                                                                      && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                      && 0 <= index1₁₃
                                                                                                                                      && index1₁₃ < ARR_SIZE₃₃
                                                                                                                                      && x₂₁ == index2₁₄
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][x₂₁] == (-1) * count₁₈)))
                                                                                                                    && (forall x₂₁: int ::
                                                                                                                          (!((exists index2₁₄: int ::
                                                                                                                                x₂₁ == index2₁₄)
                                                                                                                          )
                                                                                                                             ==> array2₃₇[index2₄₈ := (-1) * count₃₉][x₂₁] == array2₃₅[x₂₁]))
                                                                                                                    && (forall x₂₂: int ::
                                                                                                                          ((exists index1₁₃: int ::
                                                                                                                                x₂₂ == index1₁₃)
                                                                                                                             ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                                                                                                                                      temp₁₅ != 0
                                                                                                                                      && count₁₈ == 200
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                      && 0 <= index2₁₄
                                                                                                                                      && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                      && 0 <= index1₁₃
                                                                                                                                      && index1₁₃ < ARR_SIZE₃₃
                                                                                                                                      && x₂₂ == index1₁₃
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][x₂₂] == (-1) * (-1) * count₁₈)
                                                                                                                              || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                                                                                                                                      temp₁₆ != 0
                                                                                                                                      && count₁₈ != 200
                                                                                                                                      && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                      && 0 <= index2₁₄
                                                                                                                                      && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                      && 0 <= index1₁₃
                                                                                                                                      && index1₁₃ < ARR_SIZE₃₃
                                                                                                                                      && x₂₂ == index1₁₃
                                                                                                                                      && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][x₂₂] == (-1) * (-1) * count₁₈)))
                                                                                                                    && (forall x₂₂: int ::
                                                                                                                          (!((exists index1₁₃: int ::
                                                                                                                                x₂₂ == index1₁₃)
                                                                                                                          )
                                                                                                                             ==> array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][x₂₂] == array1₃₄[x₂₂]))
                                                                                                                    && (forall count₁₈: int ::
                                                                                                                            !((exists index1₁₃: int, index2₁₄: int, temp₁₅: int ::
                                                                                                                                    temp₁₅ == 0
                                                                                                                                    && count₁₈ == 200
                                                                                                                                    && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                    && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                    && 0 <= index2₁₄
                                                                                                                                    && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                    && 0 <= index1₁₃
                                                                                                                                    && index1₁₃ < ARR_SIZE₃₃)
                                                                                                                            )
                                                                                                                            && !((exists index1₁₃: int, index2₁₄: int, temp₁₆: int ::
                                                                                                                                    temp₁₆ == 0
                                                                                                                                    && count₁₈ != 200
                                                                                                                                    && array2₃₇[index2₄₈ := (-1) * count₃₉][index2₁₄] == 0
                                                                                                                                    && array1₄₁[index1₄₇ := (-1) * (-1) * count₃₉][index1₁₃] == 0
                                                                                                                                    && 0 <= index2₁₄
                                                                                                                                    && index2₁₄ < ARR_SIZE₃₃
                                                                                                                                    && 0 <= index1₁₃
                                                                                                                                    && index1₁₃ < ARR_SIZE₃₃)
                                                                                                                            ))
                                                                                                                    && true
                                                                                                                    && (true
                                                                                                                       ==> true))))))))))))))
                                                          && (!(1 != 0
                                                          )
                                                             ==> true
                                                              && (true
                                                                 ==> true
                                                                  && 0 <= 0
                                                                  && 0 <= ARR_SIZE₃₃
                                                                  && (forall count₃₀: int ::
                                                                        (  count₃₀ <= count₃₀
                                                                          && 0 <= count₃₀
                                                                          && count₃₀ < 0
                                                                           ==> count₃₀ < ARR_SIZE₃₃))
                                                                  && (forall sum₄₃: int, count₄₄: int ::
                                                                        (  true
                                                                          && 0 <= count₄₄
                                                                          && count₄₄ <= ARR_SIZE₃₃
                                                                          && (forall count₃₀: int ::
                                                                                (  count₃₀ <= count₃₀
                                                                                  && 0 <= count₃₀
                                                                                  && count₃₀ < count₄₄
                                                                                   ==> count₃₀ < ARR_SIZE₃₃))
                                                                           ==> (count₄₄ < ARR_SIZE₃₃
                                                                               ==> true
                                                                                && 0 <= count₄₄ + 1
                                                                                && count₄₄ + 1 <= ARR_SIZE₃₃
                                                                                && (forall count₃₀: int ::
                                                                                      (  count₃₀ <= count₃₀
                                                                                        && 0 <= count₃₀
                                                                                        && count₃₀ < count₄₄ + 1
                                                                                         ==> count₃₀ < ARR_SIZE₃₃))
                                                                                && true
                                                                                && (true
                                                                                   ==> true))
                                                                            && (!(count₄₄ < ARR_SIZE₃₃
                                                                            )
                                                                               ==> true
                                                                                && (true
                                                                                   ==> sum₄₃ == 0
                                                                                    && (true
                                                                                       ==> true)))))))))))))))))));

