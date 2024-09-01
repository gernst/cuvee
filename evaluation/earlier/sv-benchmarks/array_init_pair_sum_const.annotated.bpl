data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall b: [int]int ::
            (forall c: [int]int ::
                    true
                    && 0 <= 0
                    && 0 <= 100000
                    && (forall x₆: int ::
                          ((exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                             ==> (exists i₅: int ::
                                    i₅ < 100000
                                    && x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < 0
                                    && a[x₆] == 1)))
                    && (forall x₆: int ::
                          (!((exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                          )
                             ==> a[x₆] == a[x₆]))
                    && (forall x₇: int ::
                          ((exists i₅: int ::
                                  x₇ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                             ==> (exists i₅: int ::
                                    i₅ < 100000
                                    && x₇ == i₅
                                    && 0 <= i₅
                                    && i₅ < 0
                                    && b[x₇] == 2)))
                    && (forall x₇: int ::
                          (!((exists i₅: int ::
                                  x₇ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                          )
                             ==> b[x₇] == b[x₇]))
                    && (forall i₅: int ::
                          (  i₅ <= i₅
                            && 0 <= i₅
                            && i₅ < 0
                             ==> i₅ < 100000))
                    && (forall a₁₇: [int]int, b₁₈: [int]int, i₁₉: int ::
                          (  true
                            && 0 <= i₁₉
                            && i₁₉ <= 100000
                            && (forall x₆: int ::
                                  ((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₉)
                                     ==> (exists i₅: int ::
                                            i₅ < 100000
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₁₉
                                            && a₁₇[x₆] == 1)))
                            && (forall x₆: int ::
                                  (!((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₉)
                                  )
                                     ==> a₁₇[x₆] == a[x₆]))
                            && (forall x₇: int ::
                                  ((exists i₅: int ::
                                          x₇ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₉)
                                     ==> (exists i₅: int ::
                                            i₅ < 100000
                                            && x₇ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₁₉
                                            && b₁₈[x₇] == 2)))
                            && (forall x₇: int ::
                                  (!((exists i₅: int ::
                                          x₇ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₉)
                                  )
                                     ==> b₁₈[x₇] == b[x₇]))
                            && (forall i₅: int ::
                                  (  i₅ <= i₅
                                    && 0 <= i₅
                                    && i₅ < i₁₉
                                     ==> i₅ < 100000))
                             ==> (i₁₉ < 100000
                                 ==> true
                                  && 0 <= i₁₉ + 1
                                  && i₁₉ + 1 <= 100000
                                  && (forall x₆: int ::
                                        ((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₉ + 1)
                                           ==> (exists i₅: int ::
                                                  i₅ < 100000
                                                  && x₆ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₉ + 1
                                                  && a₁₇[i₁₉ := 1][x₆] == 1)))
                                  && (forall x₆: int ::
                                        (!((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₉ + 1)
                                        )
                                           ==> a₁₇[i₁₉ := 1][x₆] == a[x₆]))
                                  && (forall x₇: int ::
                                        ((exists i₅: int ::
                                                x₇ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₉ + 1)
                                           ==> (exists i₅: int ::
                                                  i₅ < 100000
                                                  && x₇ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₉ + 1
                                                  && b₁₈[i₁₉ := 2][x₇] == 2)))
                                  && (forall x₇: int ::
                                        (!((exists i₅: int ::
                                                x₇ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₉ + 1)
                                        )
                                           ==> b₁₈[i₁₉ := 2][x₇] == b[x₇]))
                                  && (forall i₅: int ::
                                        (  i₅ <= i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₉ + 1
                                           ==> i₅ < 100000))
                                  && true
                                  && (true
                                     ==> true))
                              && (!(i₁₉ < 100000
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= 100000
                                      && (forall x₁₂: int ::
                                            ((exists i₁₁: int ::
                                                    x₁₂ == i₁₁
                                                    && 0 <= i₁₁
                                                    && i₁₁ < 0)
                                               ==> (exists i₁₁: int ::
                                                      i₁₁ < 100000
                                                      && x₁₂ == i₁₁
                                                      && 0 <= i₁₁
                                                      && i₁₁ < 0
                                                      && c[x₁₂] == b₁₈[i₁₁] + a₁₇[i₁₁])))
                                      && (forall x₁₂: int ::
                                            (!((exists i₁₁: int ::
                                                    x₁₂ == i₁₁
                                                    && 0 <= i₁₁
                                                    && i₁₁ < 0)
                                            )
                                               ==> c[x₁₂] == c[x₁₂]))
                                      && (forall i₁₁: int ::
                                            (  i₁₁ <= i₁₁
                                              && 0 <= i₁₁
                                              && i₁₁ < 0
                                               ==> i₁₁ < 100000))
                                      && (forall c₂₀: [int]int, i₂₁: int ::
                                            (  true
                                              && 0 <= i₂₁
                                              && i₂₁ <= 100000
                                              && (forall x₁₂: int ::
                                                    ((exists i₁₁: int ::
                                                            x₁₂ == i₁₁
                                                            && 0 <= i₁₁
                                                            && i₁₁ < i₂₁)
                                                       ==> (exists i₁₁: int ::
                                                              i₁₁ < 100000
                                                              && x₁₂ == i₁₁
                                                              && 0 <= i₁₁
                                                              && i₁₁ < i₂₁
                                                              && c₂₀[x₁₂] == b₁₈[i₁₁] + a₁₇[i₁₁])))
                                              && (forall x₁₂: int ::
                                                    (!((exists i₁₁: int ::
                                                            x₁₂ == i₁₁
                                                            && 0 <= i₁₁
                                                            && i₁₁ < i₂₁)
                                                    )
                                                       ==> c₂₀[x₁₂] == c[x₁₂]))
                                              && (forall i₁₁: int ::
                                                    (  i₁₁ <= i₁₁
                                                      && 0 <= i₁₁
                                                      && i₁₁ < i₂₁
                                                       ==> i₁₁ < 100000))
                                               ==> (i₂₁ < 100000
                                                   ==> true
                                                    && 0 <= i₂₁ + 1
                                                    && i₂₁ + 1 <= 100000
                                                    && (forall x₁₂: int ::
                                                          ((exists i₁₁: int ::
                                                                  x₁₂ == i₁₁
                                                                  && 0 <= i₁₁
                                                                  && i₁₁ < i₂₁ + 1)
                                                             ==> (exists i₁₁: int ::
                                                                    i₁₁ < 100000
                                                                    && x₁₂ == i₁₁
                                                                    && 0 <= i₁₁
                                                                    && i₁₁ < i₂₁ + 1
                                                                    && c₂₀[i₂₁ := a₁₇[i₂₁] + b₁₈[i₂₁]][x₁₂] == b₁₈[i₁₁] + a₁₇[i₁₁])))
                                                    && (forall x₁₂: int ::
                                                          (!((exists i₁₁: int ::
                                                                  x₁₂ == i₁₁
                                                                  && 0 <= i₁₁
                                                                  && i₁₁ < i₂₁ + 1)
                                                          )
                                                             ==> c₂₀[i₂₁ := a₁₇[i₂₁] + b₁₈[i₂₁]][x₁₂] == c[x₁₂]))
                                                    && (forall i₁₁: int ::
                                                          (  i₁₁ <= i₁₁
                                                            && 0 <= i₁₁
                                                            && i₁₁ < i₂₁ + 1
                                                             ==> i₁₁ < 100000))
                                                    && true
                                                    && (true
                                                       ==> true))
                                                && (!(i₂₁ < 100000
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 1 <= 1
                                                        && 1 <= 100000
                                                        && (forall i₁₅: int ::
                                                              (  i₁₅ <= i₁₅
                                                                && 1 <= i₁₅
                                                                && i₁₅ < 1
                                                                 ==> i₁₅ < 100000))
                                                        && (forall i₂₂: int ::
                                                              (  true
                                                                && 1 <= i₂₂
                                                                && i₂₂ <= 100000
                                                                && (forall i₁₅: int ::
                                                                      (  i₁₅ <= i₁₅
                                                                        && 1 <= i₁₅
                                                                        && i₁₅ < i₂₂
                                                                         ==> i₁₅ < 100000))
                                                                 ==> (i₂₂ < 100000
                                                                     ==> 3 <= c₂₀[i₂₂]
                                                                      && (true
                                                                         ==> true
                                                                          && 1 <= i₂₂ + 1
                                                                          && i₂₂ + 1 <= 100000
                                                                          && (forall i₁₅: int ::
                                                                                (  i₁₅ <= i₁₅
                                                                                  && 1 <= i₁₅
                                                                                  && i₁₅ < i₂₂ + 1
                                                                                   ==> i₁₅ < 100000))
                                                                          && true
                                                                          && (true
                                                                             ==> true)))
                                                                  && (!(i₂₂ < 100000
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true)))))))))))))));

