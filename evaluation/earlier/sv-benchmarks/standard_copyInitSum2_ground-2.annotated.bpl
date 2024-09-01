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
              && (forall a₁₈: [int]int, i₁₉: int ::
                    (  true
                      && 0 <= i₁₉
                      && i₁₉ <= 100000
                      && (forall x₄: int ::
                            ((exists i₃: int ::
                                    x₄ == i₃
                                    && 0 <= i₃
                                    && i₃ < i₁₉)
                               ==> (exists i₃: int ::
                                      i₃ < 100000
                                      && x₄ == i₃
                                      && 0 <= i₃
                                      && i₃ < i₁₉
                                      && a₁₈[x₄] == 42)))
                      && (forall x₄: int ::
                            (!((exists i₃: int ::
                                    x₄ == i₃
                                    && 0 <= i₃
                                    && i₃ < i₁₉)
                            )
                               ==> a₁₈[x₄] == a[x₄]))
                      && (forall i₃: int ::
                            (  i₃ <= i₃
                              && 0 <= i₃
                              && i₃ < i₁₉
                               ==> i₃ < 100000))
                       ==> (i₁₉ < 100000
                           ==> true
                            && 0 <= i₁₉ + 1
                            && i₁₉ + 1 <= 100000
                            && (forall x₄: int ::
                                  ((exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₁₉ + 1)
                                     ==> (exists i₃: int ::
                                            i₃ < 100000
                                            && x₄ == i₃
                                            && 0 <= i₃
                                            && i₃ < i₁₉ + 1
                                            && a₁₈[i₁₉ := 42][x₄] == 42)))
                            && (forall x₄: int ::
                                  (!((exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₁₉ + 1)
                                  )
                                     ==> a₁₈[i₁₉ := 42][x₄] == a[x₄]))
                            && (forall i₃: int ::
                                  (  i₃ <= i₃
                                    && 0 <= i₃
                                    && i₃ < i₁₉ + 1
                                     ==> i₃ < 100000))
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
                                                && b[x₈] == a₁₈[i₇])))
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
                                && (forall b₂₀: [int]int, i₂₁: int ::
                                      (  true
                                        && 0 <= i₂₁
                                        && i₂₁ <= 100000
                                        && (forall x₈: int ::
                                              ((exists i₇: int ::
                                                      x₈ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₂₁)
                                                 ==> (exists i₇: int ::
                                                        i₇ < 100000
                                                        && x₈ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₂₁
                                                        && b₂₀[x₈] == a₁₈[i₇])))
                                        && (forall x₈: int ::
                                              (!((exists i₇: int ::
                                                      x₈ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₂₁)
                                              )
                                                 ==> b₂₀[x₈] == b[x₈]))
                                        && (forall i₇: int ::
                                              (  i₇ <= i₇
                                                && 0 <= i₇
                                                && i₇ < i₂₁
                                                 ==> i₇ < 100000))
                                         ==> (i₂₁ < 100000
                                             ==> true
                                              && 0 <= i₂₁ + 1
                                              && i₂₁ + 1 <= 100000
                                              && (forall x₈: int ::
                                                    ((exists i₇: int ::
                                                            x₈ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₂₁ + 1)
                                                       ==> (exists i₇: int ::
                                                              i₇ < 100000
                                                              && x₈ == i₇
                                                              && 0 <= i₇
                                                              && i₇ < i₂₁ + 1
                                                              && b₂₀[i₂₁ := a₁₈[i₂₁]][x₈] == a₁₈[i₇])))
                                              && (forall x₈: int ::
                                                    (!((exists i₇: int ::
                                                            x₈ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₂₁ + 1)
                                                    )
                                                       ==> b₂₀[i₂₁ := a₁₈[i₂₁]][x₈] == b[x₈]))
                                              && (forall i₇: int ::
                                                    (  i₇ <= i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₂₁ + 1
                                                       ==> i₇ < 100000))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(i₂₁ < 100000
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
                                                                  && b₂₀[x₁₂] == b₂₀[i₁₁] + i₁₁)))
                                                  && (forall x₁₂: int ::
                                                        (!((exists i₁₁: int ::
                                                                x₁₂ == i₁₁
                                                                && 0 <= i₁₁
                                                                && i₁₁ < 0)
                                                        )
                                                           ==> b₂₀[x₁₂] == b₂₀[x₁₂]))
                                                  && (forall i₁₁: int ::
                                                        (  i₁₁ <= i₁₁
                                                          && 0 <= i₁₁
                                                          && i₁₁ < 0
                                                           ==> i₁₁ < 100000))
                                                  && (forall b₂₂: [int]int, i₂₃: int ::
                                                        (  true
                                                          && 0 <= i₂₃
                                                          && i₂₃ <= 100000
                                                          && (forall x₁₂: int ::
                                                                ((exists i₁₁: int ::
                                                                        x₁₂ == i₁₁
                                                                        && 0 <= i₁₁
                                                                        && i₁₁ < i₂₃)
                                                                   ==> (exists i₁₁: int ::
                                                                          i₁₁ < 100000
                                                                          && x₁₂ == i₁₁
                                                                          && 0 <= i₁₁
                                                                          && i₁₁ < i₂₃
                                                                          && b₂₂[x₁₂] == b₂₀[i₁₁] + i₁₁)))
                                                          && (forall x₁₂: int ::
                                                                (!((exists i₁₁: int ::
                                                                        x₁₂ == i₁₁
                                                                        && 0 <= i₁₁
                                                                        && i₁₁ < i₂₃)
                                                                )
                                                                   ==> b₂₂[x₁₂] == b₂₀[x₁₂]))
                                                          && (forall i₁₁: int ::
                                                                (  i₁₁ <= i₁₁
                                                                  && 0 <= i₁₁
                                                                  && i₁₁ < i₂₃
                                                                   ==> i₁₁ < 100000))
                                                           ==> (i₂₃ < 100000
                                                               ==> true
                                                                && 0 <= i₂₃ + 1
                                                                && i₂₃ + 1 <= 100000
                                                                && (forall x₁₂: int ::
                                                                      ((exists i₁₁: int ::
                                                                              x₁₂ == i₁₁
                                                                              && 0 <= i₁₁
                                                                              && i₁₁ < i₂₃ + 1)
                                                                         ==> (exists i₁₁: int ::
                                                                                i₁₁ < 100000
                                                                                && x₁₂ == i₁₁
                                                                                && 0 <= i₁₁
                                                                                && i₁₁ < i₂₃ + 1
                                                                                && b₂₂[i₂₃ := b₂₂[i₂₃] + i₂₃][x₁₂] == b₂₀[i₁₁] + i₁₁)))
                                                                && (forall x₁₂: int ::
                                                                      (!((exists i₁₁: int ::
                                                                              x₁₂ == i₁₁
                                                                              && 0 <= i₁₁
                                                                              && i₁₁ < i₂₃ + 1)
                                                                      )
                                                                         ==> b₂₂[i₂₃ := b₂₂[i₂₃] + i₂₃][x₁₂] == b₂₀[x₁₂]))
                                                                && (forall i₁₁: int ::
                                                                      (  i₁₁ <= i₁₁
                                                                        && 0 <= i₁₁
                                                                        && i₁₁ < i₂₃ + 1
                                                                         ==> i₁₁ < 100000))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(i₂₃ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= 0
                                                                    && 0 <= 100000
                                                                    && (forall x₁₆: int ::
                                                                          (  x₁₆ <= x₁₆
                                                                            && 0 <= x₁₆
                                                                            && x₁₆ < 0
                                                                             ==> x₁₆ < 100000))
                                                                    && (forall x₂₄: int ::
                                                                          (  true
                                                                            && 0 <= x₂₄
                                                                            && x₂₄ <= 100000
                                                                            && (forall x₁₆: int ::
                                                                                  (  x₁₆ <= x₁₆
                                                                                    && 0 <= x₁₆
                                                                                    && x₁₆ < x₂₄
                                                                                     ==> x₁₆ < 100000))
                                                                             ==> (x₂₄ < 100000
                                                                                 ==> b₂₂[x₂₄] == 42 + x₂₄
                                                                                  && (true
                                                                                     ==> true
                                                                                      && 0 <= x₂₄ + 1
                                                                                      && x₂₄ + 1 <= 100000
                                                                                      && (forall x₁₆: int ::
                                                                                            (  x₁₆ <= x₁₆
                                                                                              && 0 <= x₁₆
                                                                                              && x₁₆ < x₂₄ + 1
                                                                                               ==> x₁₆ < 100000))
                                                                                      && true
                                                                                      && (true
                                                                                         ==> true)))
                                                                              && (!(x₂₄ < 100000
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true))))))))))))))))));

