data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall b: [int]int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₄: int ::
                    ((exists i₃: int ::
                            x₄ == i₃
                            && 0 <= i₃
                            && i₃ < 0)
                       ==> (exists i₃: int ::
                              i₃ < 100000
                              && x₄ == i₃
                              && 0 <= i₃
                              && i₃ < 0
                              && a[x₄] == 42)))
              && (forall x₄: int ::
                    (!((exists i₃: int ::
                            x₄ == i₃
                            && 0 <= i₃
                            && i₃ < 0)
                    )
                       ==> a[x₄] == a[x₄]))
              && (forall i₃: int ::
                    (  i₃ <= i₃
                      && 0 <= i₃
                      && i₃ < 0
                       ==> i₃ < 100000))
              && (forall a₁₄: [int]int, i₁₅: int ::
                    (  true
                      && 0 <= i₁₅
                      && i₁₅ <= 100000
                      && (forall x₄: int ::
                            ((exists i₃: int ::
                                    x₄ == i₃
                                    && 0 <= i₃
                                    && i₃ < i₁₅)
                               ==> (exists i₃: int ::
                                      i₃ < 100000
                                      && x₄ == i₃
                                      && 0 <= i₃
                                      && i₃ < i₁₅
                                      && a₁₄[x₄] == 42)))
                      && (forall x₄: int ::
                            (!((exists i₃: int ::
                                    x₄ == i₃
                                    && 0 <= i₃
                                    && i₃ < i₁₅)
                            )
                               ==> a₁₄[x₄] == a[x₄]))
                      && (forall i₃: int ::
                            (  i₃ <= i₃
                              && 0 <= i₃
                              && i₃ < i₁₅
                               ==> i₃ < 100000))
                       ==> (i₁₅ < 100000
                           ==> true
                            && 0 <= i₁₅ + 1
                            && i₁₅ + 1 <= 100000
                            && (forall x₄: int ::
                                  ((exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₁₅ + 1)
                                     ==> (exists i₃: int ::
                                            i₃ < 100000
                                            && x₄ == i₃
                                            && 0 <= i₃
                                            && i₃ < i₁₅ + 1
                                            && a₁₄[i₁₅ := 42][x₄] == 42)))
                            && (forall x₄: int ::
                                  (!((exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₁₅ + 1)
                                  )
                                     ==> a₁₄[i₁₅ := 42][x₄] == a[x₄]))
                            && (forall i₃: int ::
                                  (  i₃ <= i₃
                                    && 0 <= i₃
                                    && i₃ < i₁₅ + 1
                                     ==> i₃ < 100000))
                            && true
                            && (true
                               ==> true))
                        && (!(i₁₅ < 100000
                        )
                           ==> true
                            && (true
                               ==> true
                                && 0 <= 0
                                && 0 <= 100000
                                && (forall x₈: int ::
                                      ((exists i₇: int ::
                                              x₈ == i₇
                                              && 0 <= i₇
                                              && i₇ < 0)
                                         ==> (exists i₇: int ::
                                                i₇ < 100000
                                                && x₈ == i₇
                                                && 0 <= i₇
                                                && i₇ < 0
                                                && b[x₈] == a₁₄[i₇])))
                                && (forall x₈: int ::
                                      (!((exists i₇: int ::
                                              x₈ == i₇
                                              && 0 <= i₇
                                              && i₇ < 0)
                                      )
                                         ==> b[x₈] == b[x₈]))
                                && (forall i₇: int ::
                                      (  i₇ <= i₇
                                        && 0 <= i₇
                                        && i₇ < 0
                                         ==> i₇ < 100000))
                                && (forall b₁₆: [int]int, i₁₇: int ::
                                      (  true
                                        && 0 <= i₁₇
                                        && i₁₇ <= 100000
                                        && (forall x₈: int ::
                                              ((exists i₇: int ::
                                                      x₈ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₇)
                                                 ==> (exists i₇: int ::
                                                        i₇ < 100000
                                                        && x₈ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇
                                                        && b₁₆[x₈] == a₁₄[i₇])))
                                        && (forall x₈: int ::
                                              (!((exists i₇: int ::
                                                      x₈ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₇)
                                              )
                                                 ==> b₁₆[x₈] == b[x₈]))
                                        && (forall i₇: int ::
                                              (  i₇ <= i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇
                                                 ==> i₇ < 100000))
                                         ==> (i₁₇ < 100000
                                             ==> true
                                              && 0 <= i₁₇ + 1
                                              && i₁₇ + 1 <= 100000
                                              && (forall x₈: int ::
                                                    ((exists i₇: int ::
                                                            x₈ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₁₇ + 1)
                                                       ==> (exists i₇: int ::
                                                              i₇ < 100000
                                                              && x₈ == i₇
                                                              && 0 <= i₇
                                                              && i₇ < i₁₇ + 1
                                                              && b₁₆[i₁₇ := a₁₄[i₁₇]][x₈] == a₁₄[i₇])))
                                              && (forall x₈: int ::
                                                    (!((exists i₇: int ::
                                                            x₈ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₁₇ + 1)
                                                    )
                                                       ==> b₁₆[i₁₇ := a₁₄[i₁₇]][x₈] == b[x₈]))
                                              && (forall i₇: int ::
                                                    (  i₇ <= i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₇ + 1
                                                       ==> i₇ < 100000))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(i₁₇ < 100000
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₁₂: int ::
                                                        (  x₁₂ <= x₁₂
                                                          && 0 <= x₁₂
                                                          && x₁₂ < 0
                                                           ==> x₁₂ < 100000))
                                                  && (forall x₁₈: int ::
                                                        (  true
                                                          && 0 <= x₁₈
                                                          && x₁₈ <= 100000
                                                          && (forall x₁₂: int ::
                                                                (  x₁₂ <= x₁₂
                                                                  && 0 <= x₁₂
                                                                  && x₁₂ < x₁₈
                                                                   ==> x₁₂ < 100000))
                                                           ==> (x₁₈ < 100000
                                                               ==> b₁₆[x₁₈] == 42
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= x₁₈ + 1
                                                                    && x₁₈ + 1 <= 100000
                                                                    && (forall x₁₂: int ::
                                                                          (  x₁₂ <= x₁₂
                                                                            && 0 <= x₁₂
                                                                            && x₁₂ < x₁₈ + 1
                                                                             ==> x₁₂ < 100000))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(x₁₈ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));

