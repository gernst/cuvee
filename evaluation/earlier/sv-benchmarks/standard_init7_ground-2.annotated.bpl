data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
        true
        && 0 <= 0
        && 0 <= 100000
        && (forall x₃: int ::
              ((exists i₂: int ::
                      x₃ == i₂
                      && 0 <= i₂
                      && i₂ < 0)
                 ==> (exists i₂: int ::
                        i₂ < 100000
                        && x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0
                        && a[x₃] == 42)))
        && (forall x₃: int ::
              (!((exists i₂: int ::
                      x₃ == i₂
                      && 0 <= i₂
                      && i₂ < 0)
              )
                 ==> a[x₃] == a[x₃]))
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < 0
                 ==> i₂ < 100000))
        && (forall a₃₃: [int]int, i₃₄: int ::
              (  true
                && 0 <= i₃₄
                && i₃₄ <= 100000
                && (forall x₃: int ::
                      ((exists i₂: int ::
                              x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₃₄)
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₃₄
                                && a₃₃[x₃] == 42)))
                && (forall x₃: int ::
                      (!((exists i₂: int ::
                              x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₃₄)
                      )
                         ==> a₃₃[x₃] == a[x₃]))
                && (forall i₂: int ::
                      (  i₂ <= i₂
                        && 0 <= i₂
                        && i₂ < i₃₄
                         ==> i₂ < 100000))
                 ==> (i₃₄ < 100000
                     ==> true
                      && 0 <= i₃₄ + 1
                      && i₃₄ + 1 <= 100000
                      && (forall x₃: int ::
                            ((exists i₂: int ::
                                    x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₃₄ + 1)
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₃₄ + 1
                                      && a₃₃[i₃₄ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                            (!((exists i₂: int ::
                                    x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₃₄ + 1)
                            )
                               ==> a₃₃[i₃₄ := 42][x₃] == a[x₃]))
                      && (forall i₂: int ::
                            (  i₂ <= i₂
                              && 0 <= i₂
                              && i₂ < i₃₄ + 1
                               ==> i₂ < 100000))
                      && true
                      && (true
                         ==> true))
                  && (!(i₃₄ < 100000
                  )
                     ==> true
                      && (true
                         ==> true
                          && 0 <= 0
                          && 0 <= 100000
                          && (forall x₇: int ::
                                ((exists i₆: int ::
                                        x₇ == i₆
                                        && 0 <= i₆
                                        && i₆ < 0)
                                   ==> (exists i₆: int ::
                                          i₆ < 100000
                                          && x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < 0
                                          && a₃₃[x₇] == 43)))
                          && (forall x₇: int ::
                                (!((exists i₆: int ::
                                        x₇ == i₆
                                        && 0 <= i₆
                                        && i₆ < 0)
                                )
                                   ==> a₃₃[x₇] == a₃₃[x₇]))
                          && (forall i₆: int ::
                                (  i₆ <= i₆
                                  && 0 <= i₆
                                  && i₆ < 0
                                   ==> i₆ < 100000))
                          && (forall a₃₅: [int]int, i₃₆: int ::
                                (  true
                                  && 0 <= i₃₆
                                  && i₃₆ <= 100000
                                  && (forall x₇: int ::
                                        ((exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₃₆)
                                           ==> (exists i₆: int ::
                                                  i₆ < 100000
                                                  && x₇ == i₆
                                                  && 0 <= i₆
                                                  && i₆ < i₃₆
                                                  && a₃₅[x₇] == 43)))
                                  && (forall x₇: int ::
                                        (!((exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₃₆)
                                        )
                                           ==> a₃₅[x₇] == a₃₃[x₇]))
                                  && (forall i₆: int ::
                                        (  i₆ <= i₆
                                          && 0 <= i₆
                                          && i₆ < i₃₆
                                           ==> i₆ < 100000))
                                   ==> (i₃₆ < 100000
                                       ==> true
                                        && 0 <= i₃₆ + 1
                                        && i₃₆ + 1 <= 100000
                                        && (forall x₇: int ::
                                              ((exists i₆: int ::
                                                      x₇ == i₆
                                                      && 0 <= i₆
                                                      && i₆ < i₃₆ + 1)
                                                 ==> (exists i₆: int ::
                                                        i₆ < 100000
                                                        && x₇ == i₆
                                                        && 0 <= i₆
                                                        && i₆ < i₃₆ + 1
                                                        && a₃₅[i₃₆ := 43][x₇] == 43)))
                                        && (forall x₇: int ::
                                              (!((exists i₆: int ::
                                                      x₇ == i₆
                                                      && 0 <= i₆
                                                      && i₆ < i₃₆ + 1)
                                              )
                                                 ==> a₃₅[i₃₆ := 43][x₇] == a₃₃[x₇]))
                                        && (forall i₆: int ::
                                              (  i₆ <= i₆
                                                && 0 <= i₆
                                                && i₆ < i₃₆ + 1
                                                 ==> i₆ < 100000))
                                        && true
                                        && (true
                                           ==> true))
                                    && (!(i₃₆ < 100000
                                    )
                                       ==> true
                                        && (true
                                           ==> true
                                            && 0 <= 0
                                            && 0 <= 100000
                                            && (forall x₁₁: int ::
                                                  ((exists i₁₀: int ::
                                                          x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < 0)
                                                     ==> (exists i₁₀: int ::
                                                            i₁₀ < 100000
                                                            && x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < 0
                                                            && a₃₅[x₁₁] == 44)))
                                            && (forall x₁₁: int ::
                                                  (!((exists i₁₀: int ::
                                                          x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < 0)
                                                  )
                                                     ==> a₃₅[x₁₁] == a₃₅[x₁₁]))
                                            && (forall i₁₀: int ::
                                                  (  i₁₀ <= i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < 0
                                                     ==> i₁₀ < 100000))
                                            && (forall a₃₇: [int]int, i₃₈: int ::
                                                  (  true
                                                    && 0 <= i₃₈
                                                    && i₃₈ <= 100000
                                                    && (forall x₁₁: int ::
                                                          ((exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₃₈)
                                                             ==> (exists i₁₀: int ::
                                                                    i₁₀ < 100000
                                                                    && x₁₁ == i₁₀
                                                                    && 0 <= i₁₀
                                                                    && i₁₀ < i₃₈
                                                                    && a₃₇[x₁₁] == 44)))
                                                    && (forall x₁₁: int ::
                                                          (!((exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₃₈)
                                                          )
                                                             ==> a₃₇[x₁₁] == a₃₅[x₁₁]))
                                                    && (forall i₁₀: int ::
                                                          (  i₁₀ <= i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₃₈
                                                             ==> i₁₀ < 100000))
                                                     ==> (i₃₈ < 100000
                                                         ==> true
                                                          && 0 <= i₃₈ + 1
                                                          && i₃₈ + 1 <= 100000
                                                          && (forall x₁₁: int ::
                                                                ((exists i₁₀: int ::
                                                                        x₁₁ == i₁₀
                                                                        && 0 <= i₁₀
                                                                        && i₁₀ < i₃₈ + 1)
                                                                   ==> (exists i₁₀: int ::
                                                                          i₁₀ < 100000
                                                                          && x₁₁ == i₁₀
                                                                          && 0 <= i₁₀
                                                                          && i₁₀ < i₃₈ + 1
                                                                          && a₃₇[i₃₈ := 44][x₁₁] == 44)))
                                                          && (forall x₁₁: int ::
                                                                (!((exists i₁₀: int ::
                                                                        x₁₁ == i₁₀
                                                                        && 0 <= i₁₀
                                                                        && i₁₀ < i₃₈ + 1)
                                                                )
                                                                   ==> a₃₇[i₃₈ := 44][x₁₁] == a₃₅[x₁₁]))
                                                          && (forall i₁₀: int ::
                                                                (  i₁₀ <= i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₃₈ + 1
                                                                   ==> i₁₀ < 100000))
                                                          && true
                                                          && (true
                                                             ==> true))
                                                      && (!(i₃₈ < 100000
                                                      )
                                                         ==> true
                                                          && (true
                                                             ==> true
                                                              && 0 <= 0
                                                              && 0 <= 100000
                                                              && (forall x₁₅: int ::
                                                                    ((exists i₁₄: int ::
                                                                            x₁₅ == i₁₄
                                                                            && 0 <= i₁₄
                                                                            && i₁₄ < 0)
                                                                       ==> (exists i₁₄: int ::
                                                                              i₁₄ < 100000
                                                                              && x₁₅ == i₁₄
                                                                              && 0 <= i₁₄
                                                                              && i₁₄ < 0
                                                                              && a₃₇[x₁₅] == 45)))
                                                              && (forall x₁₅: int ::
                                                                    (!((exists i₁₄: int ::
                                                                            x₁₅ == i₁₄
                                                                            && 0 <= i₁₄
                                                                            && i₁₄ < 0)
                                                                    )
                                                                       ==> a₃₇[x₁₅] == a₃₇[x₁₅]))
                                                              && (forall i₁₄: int ::
                                                                    (  i₁₄ <= i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < 0
                                                                       ==> i₁₄ < 100000))
                                                              && (forall a₃₉: [int]int, i₄₀: int ::
                                                                    (  true
                                                                      && 0 <= i₄₀
                                                                      && i₄₀ <= 100000
                                                                      && (forall x₁₅: int ::
                                                                            ((exists i₁₄: int ::
                                                                                    x₁₅ == i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₄₀)
                                                                               ==> (exists i₁₄: int ::
                                                                                      i₁₄ < 100000
                                                                                      && x₁₅ == i₁₄
                                                                                      && 0 <= i₁₄
                                                                                      && i₁₄ < i₄₀
                                                                                      && a₃₉[x₁₅] == 45)))
                                                                      && (forall x₁₅: int ::
                                                                            (!((exists i₁₄: int ::
                                                                                    x₁₅ == i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₄₀)
                                                                            )
                                                                               ==> a₃₉[x₁₅] == a₃₇[x₁₅]))
                                                                      && (forall i₁₄: int ::
                                                                            (  i₁₄ <= i₁₄
                                                                              && 0 <= i₁₄
                                                                              && i₁₄ < i₄₀
                                                                               ==> i₁₄ < 100000))
                                                                       ==> (i₄₀ < 100000
                                                                           ==> true
                                                                            && 0 <= i₄₀ + 1
                                                                            && i₄₀ + 1 <= 100000
                                                                            && (forall x₁₅: int ::
                                                                                  ((exists i₁₄: int ::
                                                                                          x₁₅ == i₁₄
                                                                                          && 0 <= i₁₄
                                                                                          && i₁₄ < i₄₀ + 1)
                                                                                     ==> (exists i₁₄: int ::
                                                                                            i₁₄ < 100000
                                                                                            && x₁₅ == i₁₄
                                                                                            && 0 <= i₁₄
                                                                                            && i₁₄ < i₄₀ + 1
                                                                                            && a₃₉[i₄₀ := 45][x₁₅] == 45)))
                                                                            && (forall x₁₅: int ::
                                                                                  (!((exists i₁₄: int ::
                                                                                          x₁₅ == i₁₄
                                                                                          && 0 <= i₁₄
                                                                                          && i₁₄ < i₄₀ + 1)
                                                                                  )
                                                                                     ==> a₃₉[i₄₀ := 45][x₁₅] == a₃₇[x₁₅]))
                                                                            && (forall i₁₄: int ::
                                                                                  (  i₁₄ <= i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₄₀ + 1
                                                                                     ==> i₁₄ < 100000))
                                                                            && true
                                                                            && (true
                                                                               ==> true))
                                                                        && (!(i₄₀ < 100000
                                                                        )
                                                                           ==> true
                                                                            && (true
                                                                               ==> true
                                                                                && 0 <= 0
                                                                                && 0 <= 100000
                                                                                && (forall x₁₉: int ::
                                                                                      ((exists i₁₈: int ::
                                                                                              x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < 0)
                                                                                         ==> (exists i₁₈: int ::
                                                                                                i₁₈ < 100000
                                                                                                && x₁₉ == i₁₈
                                                                                                && 0 <= i₁₈
                                                                                                && i₁₈ < 0
                                                                                                && a₃₉[x₁₉] == 46)))
                                                                                && (forall x₁₉: int ::
                                                                                      (!((exists i₁₈: int ::
                                                                                              x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < 0)
                                                                                      )
                                                                                         ==> a₃₉[x₁₉] == a₃₉[x₁₉]))
                                                                                && (forall i₁₈: int ::
                                                                                      (  i₁₈ <= i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < 0
                                                                                         ==> i₁₈ < 100000))
                                                                                && (forall a₄₁: [int]int, i₄₂: int ::
                                                                                      (  true
                                                                                        && 0 <= i₄₂
                                                                                        && i₄₂ <= 100000
                                                                                        && (forall x₁₉: int ::
                                                                                              ((exists i₁₈: int ::
                                                                                                      x₁₉ == i₁₈
                                                                                                      && 0 <= i₁₈
                                                                                                      && i₁₈ < i₄₂)
                                                                                                 ==> (exists i₁₈: int ::
                                                                                                        i₁₈ < 100000
                                                                                                        && x₁₉ == i₁₈
                                                                                                        && 0 <= i₁₈
                                                                                                        && i₁₈ < i₄₂
                                                                                                        && a₄₁[x₁₉] == 46)))
                                                                                        && (forall x₁₉: int ::
                                                                                              (!((exists i₁₈: int ::
                                                                                                      x₁₉ == i₁₈
                                                                                                      && 0 <= i₁₈
                                                                                                      && i₁₈ < i₄₂)
                                                                                              )
                                                                                                 ==> a₄₁[x₁₉] == a₃₉[x₁₉]))
                                                                                        && (forall i₁₈: int ::
                                                                                              (  i₁₈ <= i₁₈
                                                                                                && 0 <= i₁₈
                                                                                                && i₁₈ < i₄₂
                                                                                                 ==> i₁₈ < 100000))
                                                                                         ==> (i₄₂ < 100000
                                                                                             ==> true
                                                                                              && 0 <= i₄₂ + 1
                                                                                              && i₄₂ + 1 <= 100000
                                                                                              && (forall x₁₉: int ::
                                                                                                    ((exists i₁₈: int ::
                                                                                                            x₁₉ == i₁₈
                                                                                                            && 0 <= i₁₈
                                                                                                            && i₁₈ < i₄₂ + 1)
                                                                                                       ==> (exists i₁₈: int ::
                                                                                                              i₁₈ < 100000
                                                                                                              && x₁₉ == i₁₈
                                                                                                              && 0 <= i₁₈
                                                                                                              && i₁₈ < i₄₂ + 1
                                                                                                              && a₄₁[i₄₂ := 46][x₁₉] == 46)))
                                                                                              && (forall x₁₉: int ::
                                                                                                    (!((exists i₁₈: int ::
                                                                                                            x₁₉ == i₁₈
                                                                                                            && 0 <= i₁₈
                                                                                                            && i₁₈ < i₄₂ + 1)
                                                                                                    )
                                                                                                       ==> a₄₁[i₄₂ := 46][x₁₉] == a₃₉[x₁₉]))
                                                                                              && (forall i₁₈: int ::
                                                                                                    (  i₁₈ <= i₁₈
                                                                                                      && 0 <= i₁₈
                                                                                                      && i₁₈ < i₄₂ + 1
                                                                                                       ==> i₁₈ < 100000))
                                                                                              && true
                                                                                              && (true
                                                                                                 ==> true))
                                                                                          && (!(i₄₂ < 100000
                                                                                          )
                                                                                             ==> true
                                                                                              && (true
                                                                                                 ==> true
                                                                                                  && 0 <= 0
                                                                                                  && 0 <= 100000
                                                                                                  && (forall x₂₃: int ::
                                                                                                        ((exists i₂₂: int ::
                                                                                                                x₂₃ == i₂₂
                                                                                                                && 0 <= i₂₂
                                                                                                                && i₂₂ < 0)
                                                                                                           ==> (exists i₂₂: int ::
                                                                                                                  i₂₂ < 100000
                                                                                                                  && x₂₃ == i₂₂
                                                                                                                  && 0 <= i₂₂
                                                                                                                  && i₂₂ < 0
                                                                                                                  && a₄₁[x₂₃] == 47)))
                                                                                                  && (forall x₂₃: int ::
                                                                                                        (!((exists i₂₂: int ::
                                                                                                                x₂₃ == i₂₂
                                                                                                                && 0 <= i₂₂
                                                                                                                && i₂₂ < 0)
                                                                                                        )
                                                                                                           ==> a₄₁[x₂₃] == a₄₁[x₂₃]))
                                                                                                  && (forall i₂₂: int ::
                                                                                                        (  i₂₂ <= i₂₂
                                                                                                          && 0 <= i₂₂
                                                                                                          && i₂₂ < 0
                                                                                                           ==> i₂₂ < 100000))
                                                                                                  && (forall a₄₃: [int]int, i₄₄: int ::
                                                                                                        (  true
                                                                                                          && 0 <= i₄₄
                                                                                                          && i₄₄ <= 100000
                                                                                                          && (forall x₂₃: int ::
                                                                                                                ((exists i₂₂: int ::
                                                                                                                        x₂₃ == i₂₂
                                                                                                                        && 0 <= i₂₂
                                                                                                                        && i₂₂ < i₄₄)
                                                                                                                   ==> (exists i₂₂: int ::
                                                                                                                          i₂₂ < 100000
                                                                                                                          && x₂₃ == i₂₂
                                                                                                                          && 0 <= i₂₂
                                                                                                                          && i₂₂ < i₄₄
                                                                                                                          && a₄₃[x₂₃] == 47)))
                                                                                                          && (forall x₂₃: int ::
                                                                                                                (!((exists i₂₂: int ::
                                                                                                                        x₂₃ == i₂₂
                                                                                                                        && 0 <= i₂₂
                                                                                                                        && i₂₂ < i₄₄)
                                                                                                                )
                                                                                                                   ==> a₄₃[x₂₃] == a₄₁[x₂₃]))
                                                                                                          && (forall i₂₂: int ::
                                                                                                                (  i₂₂ <= i₂₂
                                                                                                                  && 0 <= i₂₂
                                                                                                                  && i₂₂ < i₄₄
                                                                                                                   ==> i₂₂ < 100000))
                                                                                                           ==> (i₄₄ < 100000
                                                                                                               ==> true
                                                                                                                && 0 <= i₄₄ + 1
                                                                                                                && i₄₄ + 1 <= 100000
                                                                                                                && (forall x₂₃: int ::
                                                                                                                      ((exists i₂₂: int ::
                                                                                                                              x₂₃ == i₂₂
                                                                                                                              && 0 <= i₂₂
                                                                                                                              && i₂₂ < i₄₄ + 1)
                                                                                                                         ==> (exists i₂₂: int ::
                                                                                                                                i₂₂ < 100000
                                                                                                                                && x₂₃ == i₂₂
                                                                                                                                && 0 <= i₂₂
                                                                                                                                && i₂₂ < i₄₄ + 1
                                                                                                                                && a₄₃[i₄₄ := 47][x₂₃] == 47)))
                                                                                                                && (forall x₂₃: int ::
                                                                                                                      (!((exists i₂₂: int ::
                                                                                                                              x₂₃ == i₂₂
                                                                                                                              && 0 <= i₂₂
                                                                                                                              && i₂₂ < i₄₄ + 1)
                                                                                                                      )
                                                                                                                         ==> a₄₃[i₄₄ := 47][x₂₃] == a₄₁[x₂₃]))
                                                                                                                && (forall i₂₂: int ::
                                                                                                                      (  i₂₂ <= i₂₂
                                                                                                                        && 0 <= i₂₂
                                                                                                                        && i₂₂ < i₄₄ + 1
                                                                                                                         ==> i₂₂ < 100000))
                                                                                                                && true
                                                                                                                && (true
                                                                                                                   ==> true))
                                                                                                            && (!(i₄₄ < 100000
                                                                                                            )
                                                                                                               ==> true
                                                                                                                && (true
                                                                                                                   ==> true
                                                                                                                    && 0 <= 0
                                                                                                                    && 0 <= 100000
                                                                                                                    && (forall x₂₇: int ::
                                                                                                                          ((exists i₂₆: int ::
                                                                                                                                  x₂₇ == i₂₆
                                                                                                                                  && 0 <= i₂₆
                                                                                                                                  && i₂₆ < 0)
                                                                                                                             ==> (exists i₂₆: int ::
                                                                                                                                    i₂₆ < 100000
                                                                                                                                    && x₂₇ == i₂₆
                                                                                                                                    && 0 <= i₂₆
                                                                                                                                    && i₂₆ < 0
                                                                                                                                    && a₄₃[x₂₇] == 48)))
                                                                                                                    && (forall x₂₇: int ::
                                                                                                                          (!((exists i₂₆: int ::
                                                                                                                                  x₂₇ == i₂₆
                                                                                                                                  && 0 <= i₂₆
                                                                                                                                  && i₂₆ < 0)
                                                                                                                          )
                                                                                                                             ==> a₄₃[x₂₇] == a₄₃[x₂₇]))
                                                                                                                    && (forall i₂₆: int ::
                                                                                                                          (  i₂₆ <= i₂₆
                                                                                                                            && 0 <= i₂₆
                                                                                                                            && i₂₆ < 0
                                                                                                                             ==> i₂₆ < 100000))
                                                                                                                    && (forall a₄₅: [int]int, i₄₆: int ::
                                                                                                                          (  true
                                                                                                                            && 0 <= i₄₆
                                                                                                                            && i₄₆ <= 100000
                                                                                                                            && (forall x₂₇: int ::
                                                                                                                                  ((exists i₂₆: int ::
                                                                                                                                          x₂₇ == i₂₆
                                                                                                                                          && 0 <= i₂₆
                                                                                                                                          && i₂₆ < i₄₆)
                                                                                                                                     ==> (exists i₂₆: int ::
                                                                                                                                            i₂₆ < 100000
                                                                                                                                            && x₂₇ == i₂₆
                                                                                                                                            && 0 <= i₂₆
                                                                                                                                            && i₂₆ < i₄₆
                                                                                                                                            && a₄₅[x₂₇] == 48)))
                                                                                                                            && (forall x₂₇: int ::
                                                                                                                                  (!((exists i₂₆: int ::
                                                                                                                                          x₂₇ == i₂₆
                                                                                                                                          && 0 <= i₂₆
                                                                                                                                          && i₂₆ < i₄₆)
                                                                                                                                  )
                                                                                                                                     ==> a₄₅[x₂₇] == a₄₃[x₂₇]))
                                                                                                                            && (forall i₂₆: int ::
                                                                                                                                  (  i₂₆ <= i₂₆
                                                                                                                                    && 0 <= i₂₆
                                                                                                                                    && i₂₆ < i₄₆
                                                                                                                                     ==> i₂₆ < 100000))
                                                                                                                             ==> (i₄₆ < 100000
                                                                                                                                 ==> true
                                                                                                                                  && 0 <= i₄₆ + 1
                                                                                                                                  && i₄₆ + 1 <= 100000
                                                                                                                                  && (forall x₂₇: int ::
                                                                                                                                        ((exists i₂₆: int ::
                                                                                                                                                x₂₇ == i₂₆
                                                                                                                                                && 0 <= i₂₆
                                                                                                                                                && i₂₆ < i₄₆ + 1)
                                                                                                                                           ==> (exists i₂₆: int ::
                                                                                                                                                  i₂₆ < 100000
                                                                                                                                                  && x₂₇ == i₂₆
                                                                                                                                                  && 0 <= i₂₆
                                                                                                                                                  && i₂₆ < i₄₆ + 1
                                                                                                                                                  && a₄₅[i₄₆ := 48][x₂₇] == 48)))
                                                                                                                                  && (forall x₂₇: int ::
                                                                                                                                        (!((exists i₂₆: int ::
                                                                                                                                                x₂₇ == i₂₆
                                                                                                                                                && 0 <= i₂₆
                                                                                                                                                && i₂₆ < i₄₆ + 1)
                                                                                                                                        )
                                                                                                                                           ==> a₄₅[i₄₆ := 48][x₂₇] == a₄₃[x₂₇]))
                                                                                                                                  && (forall i₂₆: int ::
                                                                                                                                        (  i₂₆ <= i₂₆
                                                                                                                                          && 0 <= i₂₆
                                                                                                                                          && i₂₆ < i₄₆ + 1
                                                                                                                                           ==> i₂₆ < 100000))
                                                                                                                                  && true
                                                                                                                                  && (true
                                                                                                                                     ==> true))
                                                                                                                              && (!(i₄₆ < 100000
                                                                                                                              )
                                                                                                                                 ==> true
                                                                                                                                  && (true
                                                                                                                                     ==> true
                                                                                                                                      && 0 <= 0
                                                                                                                                      && 0 <= 100000
                                                                                                                                      && (forall x₃₁: int ::
                                                                                                                                            (  x₃₁ <= x₃₁
                                                                                                                                              && 0 <= x₃₁
                                                                                                                                              && x₃₁ < 0
                                                                                                                                               ==> x₃₁ < 100000))
                                                                                                                                      && (forall x₄₇: int ::
                                                                                                                                            (  true
                                                                                                                                              && 0 <= x₄₇
                                                                                                                                              && x₄₇ <= 100000
                                                                                                                                              && (forall x₃₁: int ::
                                                                                                                                                    (  x₃₁ <= x₃₁
                                                                                                                                                      && 0 <= x₃₁
                                                                                                                                                      && x₃₁ < x₄₇
                                                                                                                                                       ==> x₃₁ < 100000))
                                                                                                                                               ==> (x₄₇ < 100000
                                                                                                                                                   ==> a₄₅[x₄₇] == 48
                                                                                                                                                    && (true
                                                                                                                                                       ==> true
                                                                                                                                                        && 0 <= x₄₇ + 1
                                                                                                                                                        && x₄₇ + 1 <= 100000
                                                                                                                                                        && (forall x₃₁: int ::
                                                                                                                                                              (  x₃₁ <= x₃₁
                                                                                                                                                                && 0 <= x₃₁
                                                                                                                                                                && x₃₁ < x₄₇ + 1
                                                                                                                                                                 ==> x₃₁ < 100000))
                                                                                                                                                        && true
                                                                                                                                                        && (true
                                                                                                                                                           ==> true)))
                                                                                                                                                && (!(x₄₇ < 100000
                                                                                                                                                )
                                                                                                                                                   ==> true
                                                                                                                                                    && (true
                                                                                                                                                       ==> true)))))))))))))))))))))))))))))))));

