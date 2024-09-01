data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (true
         ==> true
          && 0 <= 0
          && 0 <= 10000000
          && (forall x₂: int ::
                ((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                   ==> (exists i₁: int ::
                          i₁ < 10000000
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < 0
                          && a[x₂] == 0)))
          && (forall x₂: int ::
                (!((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                )
                   ==> a[x₂] == a[x₂]))
          && (forall i₁: int ::
                (  i₁ <= i₁
                  && 0 <= i₁
                  && i₁ < 0
                   ==> i₁ < 10000000))
          && (forall a₁₁: [int]int, i₁₂: int ::
                (  true
                  && 0 <= i₁₂
                  && i₁₂ <= 10000000
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₁₂)
                           ==> (exists i₁: int ::
                                  i₁ < 10000000
                                  && x₂ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₁₂
                                  && a₁₁[x₂] == 0)))
                  && (forall x₂: int ::
                        (!((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₁₂)
                        )
                           ==> a₁₁[x₂] == a[x₂]))
                  && (forall i₁: int ::
                        (  i₁ <= i₁
                          && 0 <= i₁
                          && i₁ < i₁₂
                           ==> i₁ < 10000000))
                   ==> (i₁₂ < 10000000
                       ==> true
                        && 0 <= i₁₂ + 1
                        && i₁₂ + 1 <= 10000000
                        && (forall x₂: int ::
                              ((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₁₂ + 1)
                                 ==> (exists i₁: int ::
                                        i₁ < 10000000
                                        && x₂ == i₁
                                        && 0 <= i₁
                                        && i₁ < i₁₂ + 1
                                        && a₁₁[i₁₂ := 0][x₂] == 0)))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₁₂ + 1)
                              )
                                 ==> a₁₁[i₁₂ := 0][x₂] == a[x₂]))
                        && (forall i₁: int ::
                              (  i₁ <= i₁
                                && 0 <= i₁
                                && i₁ < i₁₂ + 1
                                 ==> i₁ < 10000000))
                        && true
                        && (true
                           ==> true))
                    && (!(i₁₂ < 10000000
                    )
                       ==> true
                        && (true
                           ==> true
                            && 0 <= 0
                            && 0 <= 10000000 / 2
                            && (forall x₆: int ::
                                  ((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < 0)
                                     ==> (exists i₅: int ::
                                            i₅ < 10000000 / 2
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < 0
                                            && a₁₁[x₆] == 10)))
                            && (forall x₆: int ::
                                  (!((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < 0)
                                  )
                                     ==> a₁₁[x₆] == a₁₁[x₆]))
                            && (forall i₅: int ::
                                  (  i₅ <= i₅
                                    && 0 <= i₅
                                    && i₅ < 0
                                     ==> i₅ < 10000000 / 2))
                            && (forall a₁₃: [int]int, i₁₄: int ::
                                  (  true
                                    && 0 <= i₁₄
                                    && i₁₄ <= 10000000 / 2
                                    && (forall x₆: int ::
                                          ((exists i₅: int ::
                                                  x₆ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₄)
                                             ==> (exists i₅: int ::
                                                    i₅ < 10000000 / 2
                                                    && x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₁₄
                                                    && a₁₃[x₆] == 10)))
                                    && (forall x₆: int ::
                                          (!((exists i₅: int ::
                                                  x₆ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₄)
                                          )
                                             ==> a₁₃[x₆] == a₁₁[x₆]))
                                    && (forall i₅: int ::
                                          (  i₅ <= i₅
                                            && 0 <= i₅
                                            && i₅ < i₁₄
                                             ==> i₅ < 10000000 / 2))
                                     ==> (i₁₄ < 10000000 / 2
                                         ==> true
                                          && 0 <= i₁₄ + 1
                                          && i₁₄ + 1 <= 10000000 / 2
                                          && (forall x₆: int ::
                                                ((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₁₄ + 1)
                                                   ==> (exists i₅: int ::
                                                          i₅ < 10000000 / 2
                                                          && x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₁₄ + 1
                                                          && a₁₃[i₁₄ := 10][x₆] == 10)))
                                          && (forall x₆: int ::
                                                (!((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₁₄ + 1)
                                                )
                                                   ==> a₁₃[i₁₄ := 10][x₆] == a₁₁[x₆]))
                                          && (forall i₅: int ::
                                                (  i₅ <= i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₄ + 1
                                                   ==> i₅ < 10000000 / 2))
                                          && true
                                          && (true
                                             ==> true))
                                      && (!(i₁₄ < 10000000 / 2
                                      )
                                         ==> true
                                          && (true
                                             ==> true
                                              && 0 <= 0
                                              && 0 <= 10000000 / 2
                                              && (forall i₉: int ::
                                                    (  i₉ <= i₉
                                                      && 0 <= i₉
                                                      && i₉ < 0
                                                       ==> i₉ < 10000000 / 2))
                                              && (forall i₁₅: int ::
                                                    (  true
                                                      && 0 <= i₁₅
                                                      && i₁₅ <= 10000000 / 2
                                                      && (forall i₉: int ::
                                                            (  i₉ <= i₉
                                                              && 0 <= i₉
                                                              && i₉ < i₁₅
                                                               ==> i₉ < 10000000 / 2))
                                                       ==> (i₁₅ < 10000000 / 2
                                                           ==> a₁₃[i₁₅] == 10
                                                            && (true
                                                               ==> true
                                                                && 0 <= i₁₅ + 1
                                                                && i₁₅ + 1 <= 10000000 / 2
                                                                && (forall i₉: int ::
                                                                      (  i₉ <= i₉
                                                                        && 0 <= i₉
                                                                        && i₉ < i₁₅ + 1
                                                                         ==> i₉ < 10000000 / 2))
                                                                && true
                                                                && (true
                                                                   ==> true)))
                                                        && (!(i₁₅ < 10000000 / 2
                                                        )
                                                           ==> true
                                                            && (true
                                                               ==> true))))))))))))));

