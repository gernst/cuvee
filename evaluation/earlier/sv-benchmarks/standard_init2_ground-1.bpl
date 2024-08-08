data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

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
        && (forall a₁₃: [int]int, i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ <= 100000
                && (forall x₃: int, i₂: int ::
                      (  x₃ == i₂
                        && 0 <= i₂
                        && i₂ < i₁₄
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₁₄
                                && a₁₃[x₃] == 42)))
                && (forall x₃: int ::
                        (exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₁₄)
                        || a₁₃[x₃] == a[x₃])
                && (forall i₂: int ::
                      (  0 <= i₂
                        && i₂ < i₁₄
                         ==> i₂ < 100000))
                 ==> (i₁₄ < 100000
                     ==> 0 <= i₁₄ + 1
                      && i₁₄ + 1 <= 100000
                      && (forall x₃: int, i₂: int ::
                            (  x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₁₄ + 1
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₁₄ + 1
                                      && a₁₃[i₁₄ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                              (exists i₂: int ::
                                      x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₁₄ + 1)
                              || a₁₃[i₁₄ := 42][x₃] == a[x₃])
                      && (forall i₂: int ::
                            (  0 <= i₂
                              && i₂ < i₁₄ + 1
                               ==> i₂ < 100000)))
                  &&   i₁₄ < 100000
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
                                      && a₁₃[x₇] == 43)))
                      && (forall x₇: int ::
                              (exists i₆: int ::
                                      x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < 0)
                              || a₁₃[x₇] == a₁₃[x₇])
                      && (forall i₆: int ::
                            (  0 <= i₆
                              && i₆ < 0
                               ==> i₆ < 100000))
                      && (forall a₁₅: [int]int, i₁₆: int ::
                            (  0 <= i₁₆
                              && i₁₆ <= 100000
                              && (forall x₇: int, i₆: int ::
                                    (  x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < i₁₆
                                       ==> (exists i₆: int ::
                                              i₆ < 100000
                                              && x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₁₆
                                              && a₁₅[x₇] == 43)))
                              && (forall x₇: int ::
                                      (exists i₆: int ::
                                              x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₁₆)
                                      || a₁₅[x₇] == a₁₃[x₇])
                              && (forall i₆: int ::
                                    (  0 <= i₆
                                      && i₆ < i₁₆
                                       ==> i₆ < 100000))
                               ==> (i₁₆ < 100000
                                   ==> 0 <= i₁₆ + 1
                                    && i₁₆ + 1 <= 100000
                                    && (forall x₇: int, i₆: int ::
                                          (  x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₁₆ + 1
                                             ==> (exists i₆: int ::
                                                    i₆ < 100000
                                                    && x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₁₆ + 1
                                                    && a₁₅[i₁₆ := 43][x₇] == 43)))
                                    && (forall x₇: int ::
                                            (exists i₆: int ::
                                                    x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₁₆ + 1)
                                            || a₁₅[i₁₆ := 43][x₇] == a₁₃[x₇])
                                    && (forall i₆: int ::
                                          (  0 <= i₆
                                            && i₆ < i₁₆ + 1
                                             ==> i₆ < 100000)))
                                &&   i₁₆ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₁₁: int ::
                                          (  0 <= x₁₁
                                            && x₁₁ < 0
                                             ==> x₁₁ < 100000))
                                    && (forall x₁₇: int ::
                                          (  0 <= x₁₇
                                            && x₁₇ <= 100000
                                            && (forall x₁₁: int ::
                                                  (  0 <= x₁₁
                                                    && x₁₁ < x₁₇
                                                     ==> x₁₁ < 100000))
                                             ==> (x₁₇ < 100000
                                               ==> a₁₅[x₁₇] == 42
                                                && 0 <= x₁₇ + 1
                                                && x₁₇ + 1 <= 100000
                                                && (forall x₁₁: int ::
                                                      (  0 <= x₁₁
                                                        && x₁₁ < x₁₇ + 1
                                                         ==> x₁₁ < 100000))))))))));

