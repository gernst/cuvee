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
        && (forall a₂₁: [int]int, i₂₂: int ::
              (  true
                && 0 <= i₂₂
                && i₂₂ <= 100000
                && (forall x₃: int ::
                      ((exists i₂: int ::
                              x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₂₂)
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₂₂
                                && a₂₁[x₃] == 42)))
                && (forall x₃: int ::
                      (!((exists i₂: int ::
                              x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₂₂)
                      )
                         ==> a₂₁[x₃] == a[x₃]))
                && (forall i₂: int ::
                      (  i₂ <= i₂
                        && 0 <= i₂
                        && i₂ < i₂₂
                         ==> i₂ < 100000))
                 ==> (i₂₂ < 100000
                     ==> true
                      && 0 <= i₂₂ + 1
                      && i₂₂ + 1 <= 100000
                      && (forall x₃: int ::
                            ((exists i₂: int ::
                                    x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₂₂ + 1)
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₂₂ + 1
                                      && a₂₁[i₂₂ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                            (!((exists i₂: int ::
                                    x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₂₂ + 1)
                            )
                               ==> a₂₁[i₂₂ := 42][x₃] == a[x₃]))
                      && (forall i₂: int ::
                            (  i₂ <= i₂
                              && 0 <= i₂
                              && i₂ < i₂₂ + 1
                               ==> i₂ < 100000))
                      && true
                      && (true
                         ==> true))
                  && (!(i₂₂ < 100000
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
                                          && a₂₁[x₇] == 43)))
                          && (forall x₇: int ::
                                (!((exists i₆: int ::
                                        x₇ == i₆
                                        && 0 <= i₆
                                        && i₆ < 0)
                                )
                                   ==> a₂₁[x₇] == a₂₁[x₇]))
                          && (forall i₆: int ::
                                (  i₆ <= i₆
                                  && 0 <= i₆
                                  && i₆ < 0
                                   ==> i₆ < 100000))
                          && (forall a₂₃: [int]int, i₂₄: int ::
                                (  true
                                  && 0 <= i₂₄
                                  && i₂₄ <= 100000
                                  && (forall x₇: int ::
                                        ((exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₂₄)
                                           ==> (exists i₆: int ::
                                                  i₆ < 100000
                                                  && x₇ == i₆
                                                  && 0 <= i₆
                                                  && i₆ < i₂₄
                                                  && a₂₃[x₇] == 43)))
                                  && (forall x₇: int ::
                                        (!((exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₂₄)
                                        )
                                           ==> a₂₃[x₇] == a₂₁[x₇]))
                                  && (forall i₆: int ::
                                        (  i₆ <= i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₄
                                           ==> i₆ < 100000))
                                   ==> (i₂₄ < 100000
                                       ==> true
                                        && 0 <= i₂₄ + 1
                                        && i₂₄ + 1 <= 100000
                                        && (forall x₇: int ::
                                              ((exists i₆: int ::
                                                      x₇ == i₆
                                                      && 0 <= i₆
                                                      && i₆ < i₂₄ + 1)
                                                 ==> (exists i₆: int ::
                                                        i₆ < 100000
                                                        && x₇ == i₆
                                                        && 0 <= i₆
                                                        && i₆ < i₂₄ + 1
                                                        && a₂₃[i₂₄ := 43][x₇] == 43)))
                                        && (forall x₇: int ::
                                              (!((exists i₆: int ::
                                                      x₇ == i₆
                                                      && 0 <= i₆
                                                      && i₆ < i₂₄ + 1)
                                              )
                                                 ==> a₂₃[i₂₄ := 43][x₇] == a₂₁[x₇]))
                                        && (forall i₆: int ::
                                              (  i₆ <= i₆
                                                && 0 <= i₆
                                                && i₆ < i₂₄ + 1
                                                 ==> i₆ < 100000))
                                        && true
                                        && (true
                                           ==> true))
                                    && (!(i₂₄ < 100000
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
                                                            && a₂₃[x₁₁] == 44)))
                                            && (forall x₁₁: int ::
                                                  (!((exists i₁₀: int ::
                                                          x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < 0)
                                                  )
                                                     ==> a₂₃[x₁₁] == a₂₃[x₁₁]))
                                            && (forall i₁₀: int ::
                                                  (  i₁₀ <= i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < 0
                                                     ==> i₁₀ < 100000))
                                            && (forall a₂₅: [int]int, i₂₆: int ::
                                                  (  true
                                                    && 0 <= i₂₆
                                                    && i₂₆ <= 100000
                                                    && (forall x₁₁: int ::
                                                          ((exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₂₆)
                                                             ==> (exists i₁₀: int ::
                                                                    i₁₀ < 100000
                                                                    && x₁₁ == i₁₀
                                                                    && 0 <= i₁₀
                                                                    && i₁₀ < i₂₆
                                                                    && a₂₅[x₁₁] == 44)))
                                                    && (forall x₁₁: int ::
                                                          (!((exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₂₆)
                                                          )
                                                             ==> a₂₅[x₁₁] == a₂₃[x₁₁]))
                                                    && (forall i₁₀: int ::
                                                          (  i₁₀ <= i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₂₆
                                                             ==> i₁₀ < 100000))
                                                     ==> (i₂₆ < 100000
                                                         ==> true
                                                          && 0 <= i₂₆ + 1
                                                          && i₂₆ + 1 <= 100000
                                                          && (forall x₁₁: int ::
                                                                ((exists i₁₀: int ::
                                                                        x₁₁ == i₁₀
                                                                        && 0 <= i₁₀
                                                                        && i₁₀ < i₂₆ + 1)
                                                                   ==> (exists i₁₀: int ::
                                                                          i₁₀ < 100000
                                                                          && x₁₁ == i₁₀
                                                                          && 0 <= i₁₀
                                                                          && i₁₀ < i₂₆ + 1
                                                                          && a₂₅[i₂₆ := 44][x₁₁] == 44)))
                                                          && (forall x₁₁: int ::
                                                                (!((exists i₁₀: int ::
                                                                        x₁₁ == i₁₀
                                                                        && 0 <= i₁₀
                                                                        && i₁₀ < i₂₆ + 1)
                                                                )
                                                                   ==> a₂₅[i₂₆ := 44][x₁₁] == a₂₃[x₁₁]))
                                                          && (forall i₁₀: int ::
                                                                (  i₁₀ <= i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₂₆ + 1
                                                                   ==> i₁₀ < 100000))
                                                          && true
                                                          && (true
                                                             ==> true))
                                                      && (!(i₂₆ < 100000
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
                                                                              && a₂₅[x₁₅] == 45)))
                                                              && (forall x₁₅: int ::
                                                                    (!((exists i₁₄: int ::
                                                                            x₁₅ == i₁₄
                                                                            && 0 <= i₁₄
                                                                            && i₁₄ < 0)
                                                                    )
                                                                       ==> a₂₅[x₁₅] == a₂₅[x₁₅]))
                                                              && (forall i₁₄: int ::
                                                                    (  i₁₄ <= i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < 0
                                                                       ==> i₁₄ < 100000))
                                                              && (forall a₂₇: [int]int, i₂₈: int ::
                                                                    (  true
                                                                      && 0 <= i₂₈
                                                                      && i₂₈ <= 100000
                                                                      && (forall x₁₅: int ::
                                                                            ((exists i₁₄: int ::
                                                                                    x₁₅ == i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₂₈)
                                                                               ==> (exists i₁₄: int ::
                                                                                      i₁₄ < 100000
                                                                                      && x₁₅ == i₁₄
                                                                                      && 0 <= i₁₄
                                                                                      && i₁₄ < i₂₈
                                                                                      && a₂₇[x₁₅] == 45)))
                                                                      && (forall x₁₅: int ::
                                                                            (!((exists i₁₄: int ::
                                                                                    x₁₅ == i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₂₈)
                                                                            )
                                                                               ==> a₂₇[x₁₅] == a₂₅[x₁₅]))
                                                                      && (forall i₁₄: int ::
                                                                            (  i₁₄ <= i₁₄
                                                                              && 0 <= i₁₄
                                                                              && i₁₄ < i₂₈
                                                                               ==> i₁₄ < 100000))
                                                                       ==> (i₂₈ < 100000
                                                                           ==> true
                                                                            && 0 <= i₂₈ + 1
                                                                            && i₂₈ + 1 <= 100000
                                                                            && (forall x₁₅: int ::
                                                                                  ((exists i₁₄: int ::
                                                                                          x₁₅ == i₁₄
                                                                                          && 0 <= i₁₄
                                                                                          && i₁₄ < i₂₈ + 1)
                                                                                     ==> (exists i₁₄: int ::
                                                                                            i₁₄ < 100000
                                                                                            && x₁₅ == i₁₄
                                                                                            && 0 <= i₁₄
                                                                                            && i₁₄ < i₂₈ + 1
                                                                                            && a₂₇[i₂₈ := 45][x₁₅] == 45)))
                                                                            && (forall x₁₅: int ::
                                                                                  (!((exists i₁₄: int ::
                                                                                          x₁₅ == i₁₄
                                                                                          && 0 <= i₁₄
                                                                                          && i₁₄ < i₂₈ + 1)
                                                                                  )
                                                                                     ==> a₂₇[i₂₈ := 45][x₁₅] == a₂₅[x₁₅]))
                                                                            && (forall i₁₄: int ::
                                                                                  (  i₁₄ <= i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₂₈ + 1
                                                                                     ==> i₁₄ < 100000))
                                                                            && true
                                                                            && (true
                                                                               ==> true))
                                                                        && (!(i₂₈ < 100000
                                                                        )
                                                                           ==> true
                                                                            && (true
                                                                               ==> true
                                                                                && 0 <= 0
                                                                                && 0 <= 100000
                                                                                && (forall x₁₉: int ::
                                                                                      (  x₁₉ <= x₁₉
                                                                                        && 0 <= x₁₉
                                                                                        && x₁₉ < 0
                                                                                         ==> x₁₉ < 100000))
                                                                                && (forall x₂₉: int ::
                                                                                      (  true
                                                                                        && 0 <= x₂₉
                                                                                        && x₂₉ <= 100000
                                                                                        && (forall x₁₉: int ::
                                                                                              (  x₁₉ <= x₁₉
                                                                                                && 0 <= x₁₉
                                                                                                && x₁₉ < x₂₉
                                                                                                 ==> x₁₉ < 100000))
                                                                                         ==> (x₂₉ < 100000
                                                                                             ==> a₂₇[x₂₉] == 45
                                                                                              && (true
                                                                                                 ==> true
                                                                                                  && 0 <= x₂₉ + 1
                                                                                                  && x₂₉ + 1 <= 100000
                                                                                                  && (forall x₁₉: int ::
                                                                                                        (  x₁₉ <= x₁₉
                                                                                                          && 0 <= x₁₉
                                                                                                          && x₁₉ < x₂₉ + 1
                                                                                                           ==> x₁₉ < 100000))
                                                                                                  && true
                                                                                                  && (true
                                                                                                     ==> true)))
                                                                                          && (!(x₂₉ < 100000
                                                                                          )
                                                                                             ==> true
                                                                                              && (true
                                                                                                 ==> true)))))))))))))))))))));

