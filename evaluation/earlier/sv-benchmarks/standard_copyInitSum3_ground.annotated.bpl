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
              && (forall a₂₂: [int]int, i₂₃: int ::
                    (  true
                      && 0 <= i₂₃
                      && i₂₃ <= 100000
                      && (forall x₄: int ::
                            ((exists i₃: int ::
                                    x₄ == i₃
                                    && 0 <= i₃
                                    && i₃ < i₂₃)
                               ==> (exists i₃: int ::
                                      i₃ < 100000
                                      && x₄ == i₃
                                      && 0 <= i₃
                                      && i₃ < i₂₃
                                      && a₂₂[x₄] == 42)))
                      && (forall x₄: int ::
                            (!((exists i₃: int ::
                                    x₄ == i₃
                                    && 0 <= i₃
                                    && i₃ < i₂₃)
                            )
                               ==> a₂₂[x₄] == a[x₄]))
                      && (forall i₃: int ::
                            (  i₃ <= i₃
                              && 0 <= i₃
                              && i₃ < i₂₃
                               ==> i₃ < 100000))
                       ==> (i₂₃ < 100000
                           ==> true
                            && 0 <= i₂₃ + 1
                            && i₂₃ + 1 <= 100000
                            && (forall x₄: int ::
                                  ((exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₂₃ + 1)
                                     ==> (exists i₃: int ::
                                            i₃ < 100000
                                            && x₄ == i₃
                                            && 0 <= i₃
                                            && i₃ < i₂₃ + 1
                                            && a₂₂[i₂₃ := 42][x₄] == 42)))
                            && (forall x₄: int ::
                                  (!((exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₂₃ + 1)
                                  )
                                     ==> a₂₂[i₂₃ := 42][x₄] == a[x₄]))
                            && (forall i₃: int ::
                                  (  i₃ <= i₃
                                    && 0 <= i₃
                                    && i₃ < i₂₃ + 1
                                     ==> i₃ < 100000))
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
                                                && b[x₈] == a₂₂[i₇])))
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
                                && (forall b₂₄: [int]int, i₂₅: int ::
                                      (  true
                                        && 0 <= i₂₅
                                        && i₂₅ <= 100000
                                        && (forall x₈: int ::
                                              ((exists i₇: int ::
                                                      x₈ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₂₅)
                                                 ==> (exists i₇: int ::
                                                        i₇ < 100000
                                                        && x₈ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₂₅
                                                        && b₂₄[x₈] == a₂₂[i₇])))
                                        && (forall x₈: int ::
                                              (!((exists i₇: int ::
                                                      x₈ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₂₅)
                                              )
                                                 ==> b₂₄[x₈] == b[x₈]))
                                        && (forall i₇: int ::
                                              (  i₇ <= i₇
                                                && 0 <= i₇
                                                && i₇ < i₂₅
                                                 ==> i₇ < 100000))
                                         ==> (i₂₅ < 100000
                                             ==> true
                                              && 0 <= i₂₅ + 1
                                              && i₂₅ + 1 <= 100000
                                              && (forall x₈: int ::
                                                    ((exists i₇: int ::
                                                            x₈ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₂₅ + 1)
                                                       ==> (exists i₇: int ::
                                                              i₇ < 100000
                                                              && x₈ == i₇
                                                              && 0 <= i₇
                                                              && i₇ < i₂₅ + 1
                                                              && b₂₄[i₂₅ := a₂₂[i₂₅]][x₈] == a₂₂[i₇])))
                                              && (forall x₈: int ::
                                                    (!((exists i₇: int ::
                                                            x₈ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₂₅ + 1)
                                                    )
                                                       ==> b₂₄[i₂₅ := a₂₂[i₂₅]][x₈] == b[x₈]))
                                              && (forall i₇: int ::
                                                    (  i₇ <= i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₂₅ + 1
                                                       ==> i₇ < 100000))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(i₂₅ < 100000
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
                                                                  && b₂₄[x₁₂] == b₂₄[i₁₁] + i₁₁)))
                                                  && (forall x₁₂: int ::
                                                        (!((exists i₁₁: int ::
                                                                x₁₂ == i₁₁
                                                                && 0 <= i₁₁
                                                                && i₁₁ < 0)
                                                        )
                                                           ==> b₂₄[x₁₂] == b₂₄[x₁₂]))
                                                  && (forall i₁₁: int ::
                                                        (  i₁₁ <= i₁₁
                                                          && 0 <= i₁₁
                                                          && i₁₁ < 0
                                                           ==> i₁₁ < 100000))
                                                  && (forall b₂₆: [int]int, i₂₇: int ::
                                                        (  true
                                                          && 0 <= i₂₇
                                                          && i₂₇ <= 100000
                                                          && (forall x₁₂: int ::
                                                                ((exists i₁₁: int ::
                                                                        x₁₂ == i₁₁
                                                                        && 0 <= i₁₁
                                                                        && i₁₁ < i₂₇)
                                                                   ==> (exists i₁₁: int ::
                                                                          i₁₁ < 100000
                                                                          && x₁₂ == i₁₁
                                                                          && 0 <= i₁₁
                                                                          && i₁₁ < i₂₇
                                                                          && b₂₆[x₁₂] == b₂₄[i₁₁] + i₁₁)))
                                                          && (forall x₁₂: int ::
                                                                (!((exists i₁₁: int ::
                                                                        x₁₂ == i₁₁
                                                                        && 0 <= i₁₁
                                                                        && i₁₁ < i₂₇)
                                                                )
                                                                   ==> b₂₆[x₁₂] == b₂₄[x₁₂]))
                                                          && (forall i₁₁: int ::
                                                                (  i₁₁ <= i₁₁
                                                                  && 0 <= i₁₁
                                                                  && i₁₁ < i₂₇
                                                                   ==> i₁₁ < 100000))
                                                           ==> (i₂₇ < 100000
                                                               ==> true
                                                                && 0 <= i₂₇ + 1
                                                                && i₂₇ + 1 <= 100000
                                                                && (forall x₁₂: int ::
                                                                      ((exists i₁₁: int ::
                                                                              x₁₂ == i₁₁
                                                                              && 0 <= i₁₁
                                                                              && i₁₁ < i₂₇ + 1)
                                                                         ==> (exists i₁₁: int ::
                                                                                i₁₁ < 100000
                                                                                && x₁₂ == i₁₁
                                                                                && 0 <= i₁₁
                                                                                && i₁₁ < i₂₇ + 1
                                                                                && b₂₆[i₂₇ := b₂₆[i₂₇] + i₂₇][x₁₂] == b₂₄[i₁₁] + i₁₁)))
                                                                && (forall x₁₂: int ::
                                                                      (!((exists i₁₁: int ::
                                                                              x₁₂ == i₁₁
                                                                              && 0 <= i₁₁
                                                                              && i₁₁ < i₂₇ + 1)
                                                                      )
                                                                         ==> b₂₆[i₂₇ := b₂₆[i₂₇] + i₂₇][x₁₂] == b₂₄[x₁₂]))
                                                                && (forall i₁₁: int ::
                                                                      (  i₁₁ <= i₁₁
                                                                        && 0 <= i₁₁
                                                                        && i₁₁ < i₂₇ + 1
                                                                         ==> i₁₁ < 100000))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(i₂₇ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= 0
                                                                    && 0 <= 100000
                                                                    && (forall x₁₆: int ::
                                                                          ((exists i₁₅: int ::
                                                                                  x₁₆ == i₁₅
                                                                                  && 0 <= i₁₅
                                                                                  && i₁₅ < 0)
                                                                             ==> (exists i₁₅: int ::
                                                                                    i₁₅ < 100000
                                                                                    && x₁₆ == i₁₅
                                                                                    && 0 <= i₁₅
                                                                                    && i₁₅ < 0
                                                                                    && b₂₆[x₁₆] == -a₂₂[i₁₅] + b₂₆[i₁₅])))
                                                                    && (forall x₁₆: int ::
                                                                          (!((exists i₁₅: int ::
                                                                                  x₁₆ == i₁₅
                                                                                  && 0 <= i₁₅
                                                                                  && i₁₅ < 0)
                                                                          )
                                                                             ==> b₂₆[x₁₆] == b₂₆[x₁₆]))
                                                                    && (forall i₁₅: int ::
                                                                          (  i₁₅ <= i₁₅
                                                                            && 0 <= i₁₅
                                                                            && i₁₅ < 0
                                                                             ==> i₁₅ < 100000))
                                                                    && (forall b₂₈: [int]int, i₂₉: int ::
                                                                          (  true
                                                                            && 0 <= i₂₉
                                                                            && i₂₉ <= 100000
                                                                            && (forall x₁₆: int ::
                                                                                  ((exists i₁₅: int ::
                                                                                          x₁₆ == i₁₅
                                                                                          && 0 <= i₁₅
                                                                                          && i₁₅ < i₂₉)
                                                                                     ==> (exists i₁₅: int ::
                                                                                            i₁₅ < 100000
                                                                                            && x₁₆ == i₁₅
                                                                                            && 0 <= i₁₅
                                                                                            && i₁₅ < i₂₉
                                                                                            && b₂₈[x₁₆] == -a₂₂[i₁₅] + b₂₆[i₁₅])))
                                                                            && (forall x₁₆: int ::
                                                                                  (!((exists i₁₅: int ::
                                                                                          x₁₆ == i₁₅
                                                                                          && 0 <= i₁₅
                                                                                          && i₁₅ < i₂₉)
                                                                                  )
                                                                                     ==> b₂₈[x₁₆] == b₂₆[x₁₆]))
                                                                            && (forall i₁₅: int ::
                                                                                  (  i₁₅ <= i₁₅
                                                                                    && 0 <= i₁₅
                                                                                    && i₁₅ < i₂₉
                                                                                     ==> i₁₅ < 100000))
                                                                             ==> (i₂₉ < 100000
                                                                                 ==> true
                                                                                  && 0 <= i₂₉ + 1
                                                                                  && i₂₉ + 1 <= 100000
                                                                                  && (forall x₁₆: int ::
                                                                                        ((exists i₁₅: int ::
                                                                                                x₁₆ == i₁₅
                                                                                                && 0 <= i₁₅
                                                                                                && i₁₅ < i₂₉ + 1)
                                                                                           ==> (exists i₁₅: int ::
                                                                                                  i₁₅ < 100000
                                                                                                  && x₁₆ == i₁₅
                                                                                                  && 0 <= i₁₅
                                                                                                  && i₁₅ < i₂₉ + 1
                                                                                                  && b₂₈[i₂₉ := b₂₈[i₂₉] - a₂₂[i₂₉]][x₁₆] == -a₂₂[i₁₅] + b₂₆[i₁₅])))
                                                                                  && (forall x₁₆: int ::
                                                                                        (!((exists i₁₅: int ::
                                                                                                x₁₆ == i₁₅
                                                                                                && 0 <= i₁₅
                                                                                                && i₁₅ < i₂₉ + 1)
                                                                                        )
                                                                                           ==> b₂₈[i₂₉ := b₂₈[i₂₉] - a₂₂[i₂₉]][x₁₆] == b₂₆[x₁₆]))
                                                                                  && (forall i₁₅: int ::
                                                                                        (  i₁₅ <= i₁₅
                                                                                          && 0 <= i₁₅
                                                                                          && i₁₅ < i₂₉ + 1
                                                                                           ==> i₁₅ < 100000))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true))
                                                                              && (!(i₂₉ < 100000
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true
                                                                                      && 0 <= 0
                                                                                      && 0 <= 100000
                                                                                      && (forall x₂₀: int ::
                                                                                            (  x₂₀ <= x₂₀
                                                                                              && 0 <= x₂₀
                                                                                              && x₂₀ < 0
                                                                                               ==> x₂₀ < 100000))
                                                                                      && (forall x₃₀: int ::
                                                                                            (  true
                                                                                              && 0 <= x₃₀
                                                                                              && x₃₀ <= 100000
                                                                                              && (forall x₂₀: int ::
                                                                                                    (  x₂₀ <= x₂₀
                                                                                                      && 0 <= x₂₀
                                                                                                      && x₂₀ < x₃₀
                                                                                                       ==> x₂₀ < 100000))
                                                                                               ==> (x₃₀ < 100000
                                                                                                   ==> b₂₈[x₃₀] == x₃₀
                                                                                                    && (true
                                                                                                       ==> true
                                                                                                        && 0 <= x₃₀ + 1
                                                                                                        && x₃₀ + 1 <= 100000
                                                                                                        && (forall x₂₀: int ::
                                                                                                              (  x₂₀ <= x₂₀
                                                                                                                && 0 <= x₂₀
                                                                                                                && x₂₀ < x₃₀ + 1
                                                                                                                 ==> x₂₀ < 100000))
                                                                                                        && true
                                                                                                        && (true
                                                                                                           ==> true)))
                                                                                                && (!(x₃₀ < 100000
                                                                                                )
                                                                                                   ==> true
                                                                                                    && (true
                                                                                                       ==> true))))))))))))))))))))));

