data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₃: int, i₂: int ::
              (  x₃ == i₂
                && 0 <= i₂
                && i₂ < 0
                 ==> (exists i₂: int ::
                        i₂ < 100000
                        && x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0
                        && a[x₃] == 42)))
        && (forall x₃: int ::
                (exists i₂: int ::
                        x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0)
                || a[x₃] == a[x₃])
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < 0
                 ==> i₂ < 100000))
        && (forall a₁₇: [int]int, i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ <= 100000
                && (forall x₃: int, i₂: int ::
                      (  x₃ == i₂
                        && 0 <= i₂
                        && i₂ < i₁₈
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₁₈
                                && a₁₇[x₃] == 42)))
                && (forall x₃: int ::
                        (exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₁₈)
                        || a₁₇[x₃] == a[x₃])
                && (forall i₂: int ::
                      (  0 <= i₂
                        && i₂ < i₁₈
                         ==> i₂ < 100000))
                 ==> (i₁₈ < 100000
                     ==> 0 <= i₁₈ + 1
                      && i₁₈ + 1 <= 100000
                      && (forall x₃: int, i₂: int ::
                            (  x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₁₈ + 1
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₁₈ + 1
                                      && a₁₇[i₁₈ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                              (exists i₂: int ::
                                      x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₁₈ + 1)
                              || a₁₇[i₁₈ := 42][x₃] == a[x₃])
                      && (forall i₂: int ::
                            (  0 <= i₂
                              && i₂ < i₁₈ + 1
                               ==> i₂ < 100000)))
                  &&   i₁₈ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₇: int, i₆: int ::
                            (  x₇ == i₆
                              && 0 <= i₆
                              && i₆ < 0
                               ==> (exists i₆: int ::
                                      i₆ < 100000
                                      && x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < 0
                                      && a₁₇[x₇] == 43)))
                      && (forall x₇: int ::
                              (exists i₆: int ::
                                      x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < 0)
                              || a₁₇[x₇] == a₁₇[x₇])
                      && (forall i₆: int ::
                            (  0 <= i₆
                              && i₆ < 0
                               ==> i₆ < 100000))
                      && (forall a₁₉: [int]int, i₂₀: int ::
                            (  0 <= i₂₀
                              && i₂₀ <= 100000
                              && (forall x₇: int, i₆: int ::
                                    (  x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < i₂₀
                                       ==> (exists i₆: int ::
                                              i₆ < 100000
                                              && x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₂₀
                                              && a₁₉[x₇] == 43)))
                              && (forall x₇: int ::
                                      (exists i₆: int ::
                                              x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₂₀)
                                      || a₁₉[x₇] == a₁₇[x₇])
                              && (forall i₆: int ::
                                    (  0 <= i₆
                                      && i₆ < i₂₀
                                       ==> i₆ < 100000))
                               ==> (i₂₀ < 100000
                                   ==> 0 <= i₂₀ + 1
                                    && i₂₀ + 1 <= 100000
                                    && (forall x₇: int, i₆: int ::
                                          (  x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₀ + 1
                                             ==> (exists i₆: int ::
                                                    i₆ < 100000
                                                    && x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₂₀ + 1
                                                    && a₁₉[i₂₀ := 43][x₇] == 43)))
                                    && (forall x₇: int ::
                                            (exists i₆: int ::
                                                    x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₂₀ + 1)
                                            || a₁₉[i₂₀ := 43][x₇] == a₁₇[x₇])
                                    && (forall i₆: int ::
                                          (  0 <= i₆
                                            && i₆ < i₂₀ + 1
                                             ==> i₆ < 100000)))
                                &&   i₂₀ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₁₁: int, i₁₀: int ::
                                          (  x₁₁ == i₁₀
                                            && 0 <= i₁₀
                                            && i₁₀ < 0
                                             ==> (exists i₁₀: int ::
                                                    i₁₀ < 100000
                                                    && x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < 0
                                                    && a₁₉[x₁₁] == 44)))
                                    && (forall x₁₁: int ::
                                            (exists i₁₀: int ::
                                                    x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < 0)
                                            || a₁₉[x₁₁] == a₁₉[x₁₁])
                                    && (forall i₁₀: int ::
                                          (  0 <= i₁₀
                                            && i₁₀ < 0
                                             ==> i₁₀ < 100000))
                                    && (forall a₂₁: [int]int, i₂₂: int ::
                                          (  0 <= i₂₂
                                            && i₂₂ <= 100000
                                            && (forall x₁₁: int, i₁₀: int ::
                                                  (  x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < i₂₂
                                                     ==> (exists i₁₀: int ::
                                                            i₁₀ < 100000
                                                            && x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₂₂
                                                            && a₂₁[x₁₁] == 44)))
                                            && (forall x₁₁: int ::
                                                    (exists i₁₀: int ::
                                                            x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₂₂)
                                                    || a₂₁[x₁₁] == a₁₉[x₁₁])
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₂₂
                                                     ==> i₁₀ < 100000))
                                             ==> (i₂₂ < 100000
                                                 ==> 0 <= i₂₂ + 1
                                                  && i₂₂ + 1 <= 100000
                                                  && (forall x₁₁: int, i₁₀: int ::
                                                        (  x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₂₂ + 1
                                                           ==> (exists i₁₀: int ::
                                                                  i₁₀ < 100000
                                                                  && x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₂₂ + 1
                                                                  && a₂₁[i₂₂ := 44][x₁₁] == 44)))
                                                  && (forall x₁₁: int ::
                                                          (exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₂₂ + 1)
                                                          || a₂₁[i₂₂ := 44][x₁₁] == a₁₉[x₁₁])
                                                  && (forall i₁₀: int ::
                                                        (  0 <= i₁₀
                                                          && i₁₀ < i₂₂ + 1
                                                           ==> i₁₀ < 100000)))
                                              &&   i₂₂ < 100000
                                                ||   0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₁₅: int ::
                                                        (  0 <= x₁₅
                                                          && x₁₅ < 0
                                                           ==> x₁₅ < 100000))
                                                  && (forall x₂₃: int ::
                                                        (  0 <= x₂₃
                                                          && x₂₃ <= 100000
                                                          && (forall x₁₅: int ::
                                                                (  0 <= x₁₅
                                                                  && x₁₅ < x₂₃
                                                                   ==> x₁₅ < 100000))
                                                           ==> (x₂₃ < 100000
                                                             ==> a₂₁[x₂₃] == 43
                                                              && 0 <= x₂₃ + 1
                                                              && x₂₃ + 1 <= 100000
                                                              && (forall x₁₅: int ::
                                                                    (  0 <= x₁₅
                                                                      && x₁₅ < x₂₃ + 1
                                                                       ==> x₁₅ < 100000))))))))))));

