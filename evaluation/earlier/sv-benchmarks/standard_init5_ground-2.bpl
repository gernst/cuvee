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
        && (forall a₂₅: [int]int, i₂₆: int ::
              (  0 <= i₂₆
                && i₂₆ <= 100000
                && (forall x₃: int, i₂: int ::
                      (  x₃ == i₂
                        && 0 <= i₂
                        && i₂ < i₂₆
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₂₆
                                && a₂₅[x₃] == 42)))
                && (forall x₃: int ::
                        (exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₂₆)
                        || a₂₅[x₃] == a[x₃])
                && (forall i₂: int ::
                      (  0 <= i₂
                        && i₂ < i₂₆
                         ==> i₂ < 100000))
                 ==> (i₂₆ < 100000
                     ==> 0 <= i₂₆ + 1
                      && i₂₆ + 1 <= 100000
                      && (forall x₃: int, i₂: int ::
                            (  x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₂₆ + 1
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₂₆ + 1
                                      && a₂₅[i₂₆ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                              (exists i₂: int ::
                                      x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₂₆ + 1)
                              || a₂₅[i₂₆ := 42][x₃] == a[x₃])
                      && (forall i₂: int ::
                            (  0 <= i₂
                              && i₂ < i₂₆ + 1
                               ==> i₂ < 100000)))
                  &&   i₂₆ < 100000
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
                                      && a₂₅[x₇] == 43)))
                      && (forall x₇: int ::
                              (exists i₆: int ::
                                      x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < 0)
                              || a₂₅[x₇] == a₂₅[x₇])
                      && (forall i₆: int ::
                            (  0 <= i₆
                              && i₆ < 0
                               ==> i₆ < 100000))
                      && (forall a₂₇: [int]int, i₂₈: int ::
                            (  0 <= i₂₈
                              && i₂₈ <= 100000
                              && (forall x₇: int, i₆: int ::
                                    (  x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < i₂₈
                                       ==> (exists i₆: int ::
                                              i₆ < 100000
                                              && x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₂₈
                                              && a₂₇[x₇] == 43)))
                              && (forall x₇: int ::
                                      (exists i₆: int ::
                                              x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₂₈)
                                      || a₂₇[x₇] == a₂₅[x₇])
                              && (forall i₆: int ::
                                    (  0 <= i₆
                                      && i₆ < i₂₈
                                       ==> i₆ < 100000))
                               ==> (i₂₈ < 100000
                                   ==> 0 <= i₂₈ + 1
                                    && i₂₈ + 1 <= 100000
                                    && (forall x₇: int, i₆: int ::
                                          (  x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₈ + 1
                                             ==> (exists i₆: int ::
                                                    i₆ < 100000
                                                    && x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₂₈ + 1
                                                    && a₂₇[i₂₈ := 43][x₇] == 43)))
                                    && (forall x₇: int ::
                                            (exists i₆: int ::
                                                    x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₂₈ + 1)
                                            || a₂₇[i₂₈ := 43][x₇] == a₂₅[x₇])
                                    && (forall i₆: int ::
                                          (  0 <= i₆
                                            && i₆ < i₂₈ + 1
                                             ==> i₆ < 100000)))
                                &&   i₂₈ < 100000
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
                                                    && a₂₇[x₁₁] == 44)))
                                    && (forall x₁₁: int ::
                                            (exists i₁₀: int ::
                                                    x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < 0)
                                            || a₂₇[x₁₁] == a₂₇[x₁₁])
                                    && (forall i₁₀: int ::
                                          (  0 <= i₁₀
                                            && i₁₀ < 0
                                             ==> i₁₀ < 100000))
                                    && (forall a₂₉: [int]int, i₃₀: int ::
                                          (  0 <= i₃₀
                                            && i₃₀ <= 100000
                                            && (forall x₁₁: int, i₁₀: int ::
                                                  (  x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < i₃₀
                                                     ==> (exists i₁₀: int ::
                                                            i₁₀ < 100000
                                                            && x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₃₀
                                                            && a₂₉[x₁₁] == 44)))
                                            && (forall x₁₁: int ::
                                                    (exists i₁₀: int ::
                                                            x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₃₀)
                                                    || a₂₉[x₁₁] == a₂₇[x₁₁])
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₃₀
                                                     ==> i₁₀ < 100000))
                                             ==> (i₃₀ < 100000
                                                 ==> 0 <= i₃₀ + 1
                                                  && i₃₀ + 1 <= 100000
                                                  && (forall x₁₁: int, i₁₀: int ::
                                                        (  x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₃₀ + 1
                                                           ==> (exists i₁₀: int ::
                                                                  i₁₀ < 100000
                                                                  && x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₃₀ + 1
                                                                  && a₂₉[i₃₀ := 44][x₁₁] == 44)))
                                                  && (forall x₁₁: int ::
                                                          (exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₃₀ + 1)
                                                          || a₂₉[i₃₀ := 44][x₁₁] == a₂₇[x₁₁])
                                                  && (forall i₁₀: int ::
                                                        (  0 <= i₁₀
                                                          && i₁₀ < i₃₀ + 1
                                                           ==> i₁₀ < 100000)))
                                              &&   i₃₀ < 100000
                                                ||   0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₁₅: int, i₁₄: int ::
                                                        (  x₁₅ == i₁₄
                                                          && 0 <= i₁₄
                                                          && i₁₄ < 0
                                                           ==> (exists i₁₄: int ::
                                                                  i₁₄ < 100000
                                                                  && x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < 0
                                                                  && a₂₉[x₁₅] == 45)))
                                                  && (forall x₁₅: int ::
                                                          (exists i₁₄: int ::
                                                                  x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < 0)
                                                          || a₂₉[x₁₅] == a₂₉[x₁₅])
                                                  && (forall i₁₄: int ::
                                                        (  0 <= i₁₄
                                                          && i₁₄ < 0
                                                           ==> i₁₄ < 100000))
                                                  && (forall a₃₁: [int]int, i₃₂: int ::
                                                        (  0 <= i₃₂
                                                          && i₃₂ <= 100000
                                                          && (forall x₁₅: int, i₁₄: int ::
                                                                (  x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < i₃₂
                                                                   ==> (exists i₁₄: int ::
                                                                          i₁₄ < 100000
                                                                          && x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₃₂
                                                                          && a₃₁[x₁₅] == 45)))
                                                          && (forall x₁₅: int ::
                                                                  (exists i₁₄: int ::
                                                                          x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₃₂)
                                                                  || a₃₁[x₁₅] == a₂₉[x₁₅])
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₃₂
                                                                   ==> i₁₄ < 100000))
                                                           ==> (i₃₂ < 100000
                                                               ==> 0 <= i₃₂ + 1
                                                                && i₃₂ + 1 <= 100000
                                                                && (forall x₁₅: int, i₁₄: int ::
                                                                      (  x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₃₂ + 1
                                                                         ==> (exists i₁₄: int ::
                                                                                i₁₄ < 100000
                                                                                && x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₃₂ + 1
                                                                                && a₃₁[i₃₂ := 45][x₁₅] == 45)))
                                                                && (forall x₁₅: int ::
                                                                        (exists i₁₄: int ::
                                                                                x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₃₂ + 1)
                                                                        || a₃₁[i₃₂ := 45][x₁₅] == a₂₉[x₁₅])
                                                                && (forall i₁₄: int ::
                                                                      (  0 <= i₁₄
                                                                        && i₁₄ < i₃₂ + 1
                                                                         ==> i₁₄ < 100000)))
                                                            &&   i₃₂ < 100000
                                                              ||   0 <= 0
                                                                && 0 <= 100000
                                                                && (forall x₁₉: int, i₁₈: int ::
                                                                      (  x₁₉ == i₁₈
                                                                        && 0 <= i₁₈
                                                                        && i₁₈ < 0
                                                                         ==> (exists i₁₈: int ::
                                                                                i₁₈ < 100000
                                                                                && x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < 0
                                                                                && a₃₁[x₁₉] == 46)))
                                                                && (forall x₁₉: int ::
                                                                        (exists i₁₈: int ::
                                                                                x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < 0)
                                                                        || a₃₁[x₁₉] == a₃₁[x₁₉])
                                                                && (forall i₁₈: int ::
                                                                      (  0 <= i₁₈
                                                                        && i₁₈ < 0
                                                                         ==> i₁₈ < 100000))
                                                                && (forall a₃₃: [int]int, i₃₄: int ::
                                                                      (  0 <= i₃₄
                                                                        && i₃₄ <= 100000
                                                                        && (forall x₁₉: int, i₁₈: int ::
                                                                              (  x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < i₃₄
                                                                                 ==> (exists i₁₈: int ::
                                                                                        i₁₈ < 100000
                                                                                        && x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < i₃₄
                                                                                        && a₃₃[x₁₉] == 46)))
                                                                        && (forall x₁₉: int ::
                                                                                (exists i₁₈: int ::
                                                                                        x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < i₃₄)
                                                                                || a₃₃[x₁₉] == a₃₁[x₁₉])
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₃₄
                                                                                 ==> i₁₈ < 100000))
                                                                         ==> (i₃₄ < 100000
                                                                             ==> 0 <= i₃₄ + 1
                                                                              && i₃₄ + 1 <= 100000
                                                                              && (forall x₁₉: int, i₁₈: int ::
                                                                                    (  x₁₉ == i₁₈
                                                                                      && 0 <= i₁₈
                                                                                      && i₁₈ < i₃₄ + 1
                                                                                       ==> (exists i₁₈: int ::
                                                                                              i₁₈ < 100000
                                                                                              && x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₃₄ + 1
                                                                                              && a₃₃[i₃₄ := 46][x₁₉] == 46)))
                                                                              && (forall x₁₉: int ::
                                                                                      (exists i₁₈: int ::
                                                                                              x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₃₄ + 1)
                                                                                      || a₃₃[i₃₄ := 46][x₁₉] == a₃₁[x₁₉])
                                                                              && (forall i₁₈: int ::
                                                                                    (  0 <= i₁₈
                                                                                      && i₁₈ < i₃₄ + 1
                                                                                       ==> i₁₈ < 100000)))
                                                                          &&   i₃₄ < 100000
                                                                            ||   0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₂₃: int ::
                                                                                    (  0 <= x₂₃
                                                                                      && x₂₃ < 0
                                                                                       ==> x₂₃ < 100000))
                                                                              && (forall x₃₅: int ::
                                                                                    (  0 <= x₃₅
                                                                                      && x₃₅ <= 100000
                                                                                      && (forall x₂₃: int ::
                                                                                            (  0 <= x₂₃
                                                                                              && x₂₃ < x₃₅
                                                                                               ==> x₂₃ < 100000))
                                                                                       ==> (x₃₅ < 100000
                                                                                         ==> a₃₃[x₃₅] == 45
                                                                                          && 0 <= x₃₅ + 1
                                                                                          && x₃₅ + 1 <= 100000
                                                                                          && (forall x₂₃: int ::
                                                                                                (  0 <= x₂₃
                                                                                                  && x₂₃ < x₃₅ + 1
                                                                                                   ==> x₂₃ < 100000))))))))))))))));

