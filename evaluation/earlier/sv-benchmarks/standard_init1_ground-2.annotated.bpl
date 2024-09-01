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
        && (forall a₉: [int]int, i₁₀: int ::
              (  true
                && 0 <= i₁₀
                && i₁₀ <= 100000
                && (forall x₃: int ::
                      ((exists i₂: int ::
                              x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₁₀)
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₁₀
                                && a₉[x₃] == 42)))
                && (forall x₃: int ::
                      (!((exists i₂: int ::
                              x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₁₀)
                      )
                         ==> a₉[x₃] == a[x₃]))
                && (forall i₂: int ::
                      (  i₂ <= i₂
                        && 0 <= i₂
                        && i₂ < i₁₀
                         ==> i₂ < 100000))
                 ==> (i₁₀ < 100000
                     ==> true
                      && 0 <= i₁₀ + 1
                      && i₁₀ + 1 <= 100000
                      && (forall x₃: int ::
                            ((exists i₂: int ::
                                    x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₁₀ + 1)
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₁₀ + 1
                                      && a₉[i₁₀ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                            (!((exists i₂: int ::
                                    x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₁₀ + 1)
                            )
                               ==> a₉[i₁₀ := 42][x₃] == a[x₃]))
                      && (forall i₂: int ::
                            (  i₂ <= i₂
                              && 0 <= i₂
                              && i₂ < i₁₀ + 1
                               ==> i₂ < 100000))
                      && true
                      && (true
                         ==> true))
                  && (!(i₁₀ < 100000
                  )
                     ==> true
                      && (true
                         ==> true
                          && 0 <= 0
                          && 0 <= 100000
                          && (forall x₇: int ::
                                (  x₇ <= x₇
                                  && 0 <= x₇
                                  && x₇ < 0
                                   ==> x₇ < 100000))
                          && (forall x₁₁: int ::
                                (  true
                                  && 0 <= x₁₁
                                  && x₁₁ <= 100000
                                  && (forall x₇: int ::
                                        (  x₇ <= x₇
                                          && 0 <= x₇
                                          && x₇ < x₁₁
                                           ==> x₇ < 100000))
                                   ==> (x₁₁ < 100000
                                       ==> a₉[x₁₁] == 42
                                        && (true
                                           ==> true
                                            && 0 <= x₁₁ + 1
                                            && x₁₁ + 1 <= 100000
                                            && (forall x₇: int ::
                                                  (  x₇ <= x₇
                                                    && 0 <= x₇
                                                    && x₇ < x₁₁ + 1
                                                     ==> x₇ < 100000))
                                            && true
                                            && (true
                                               ==> true)))
                                    && (!(x₁₁ < 100000
                                    )
                                       ==> true
                                        && (true
                                           ==> true)))))))));

