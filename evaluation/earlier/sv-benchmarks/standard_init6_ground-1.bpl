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
        && (forall a₂₉: [int]int, i₃₀: int ::
              (  0 <= i₃₀
                && i₃₀ <= 100000
                && (forall x₃: int, i₂: int ::
                      (  x₃ == i₂
                        && 0 <= i₂
                        && i₂ < i₃₀
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₃₀
                                && a₂₉[x₃] == 42)))
                && (forall x₃: int ::
                        (exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₃₀)
                        || a₂₉[x₃] == a[x₃])
                && (forall i₂: int ::
                      (  0 <= i₂
                        && i₂ < i₃₀
                         ==> i₂ < 100000))
                 ==> (i₃₀ < 100000
                     ==> 0 <= i₃₀ + 1
                      && i₃₀ + 1 <= 100000
                      && (forall x₃: int, i₂: int ::
                            (  x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₃₀ + 1
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₃₀ + 1
                                      && a₂₉[i₃₀ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                              (exists i₂: int ::
                                      x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₃₀ + 1)
                              || a₂₉[i₃₀ := 42][x₃] == a[x₃])
                      && (forall i₂: int ::
                            (  0 <= i₂
                              && i₂ < i₃₀ + 1
                               ==> i₂ < 100000)))
                  &&   i₃₀ < 100000
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
                                      && a₂₉[x₇] == 43)))
                      && (forall x₇: int ::
                              (exists i₆: int ::
                                      x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < 0)
                              || a₂₉[x₇] == a₂₉[x₇])
                      && (forall i₆: int ::
                            (  0 <= i₆
                              && i₆ < 0
                               ==> i₆ < 100000))
                      && (forall a₃₁: [int]int, i₃₂: int ::
                            (  0 <= i₃₂
                              && i₃₂ <= 100000
                              && (forall x₇: int, i₆: int ::
                                    (  x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < i₃₂
                                       ==> (exists i₆: int ::
                                              i₆ < 100000
                                              && x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₃₂
                                              && a₃₁[x₇] == 43)))
                              && (forall x₇: int ::
                                      (exists i₆: int ::
                                              x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₃₂)
                                      || a₃₁[x₇] == a₂₉[x₇])
                              && (forall i₆: int ::
                                    (  0 <= i₆
                                      && i₆ < i₃₂
                                       ==> i₆ < 100000))
                               ==> (i₃₂ < 100000
                                   ==> 0 <= i₃₂ + 1
                                    && i₃₂ + 1 <= 100000
                                    && (forall x₇: int, i₆: int ::
                                          (  x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₃₂ + 1
                                             ==> (exists i₆: int ::
                                                    i₆ < 100000
                                                    && x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₃₂ + 1
                                                    && a₃₁[i₃₂ := 43][x₇] == 43)))
                                    && (forall x₇: int ::
                                            (exists i₆: int ::
                                                    x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₃₂ + 1)
                                            || a₃₁[i₃₂ := 43][x₇] == a₂₉[x₇])
                                    && (forall i₆: int ::
                                          (  0 <= i₆
                                            && i₆ < i₃₂ + 1
                                             ==> i₆ < 100000)))
                                &&   i₃₂ < 100000
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
                                                    && a₃₁[x₁₁] == 44)))
                                    && (forall x₁₁: int ::
                                            (exists i₁₀: int ::
                                                    x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < 0)
                                            || a₃₁[x₁₁] == a₃₁[x₁₁])
                                    && (forall i₁₀: int ::
                                          (  0 <= i₁₀
                                            && i₁₀ < 0
                                             ==> i₁₀ < 100000))
                                    && (forall a₃₃: [int]int, i₃₄: int ::
                                          (  0 <= i₃₄
                                            && i₃₄ <= 100000
                                            && (forall x₁₁: int, i₁₀: int ::
                                                  (  x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < i₃₄
                                                     ==> (exists i₁₀: int ::
                                                            i₁₀ < 100000
                                                            && x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₃₄
                                                            && a₃₃[x₁₁] == 44)))
                                            && (forall x₁₁: int ::
                                                    (exists i₁₀: int ::
                                                            x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₃₄)
                                                    || a₃₃[x₁₁] == a₃₁[x₁₁])
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₃₄
                                                     ==> i₁₀ < 100000))
                                             ==> (i₃₄ < 100000
                                                 ==> 0 <= i₃₄ + 1
                                                  && i₃₄ + 1 <= 100000
                                                  && (forall x₁₁: int, i₁₀: int ::
                                                        (  x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₃₄ + 1
                                                           ==> (exists i₁₀: int ::
                                                                  i₁₀ < 100000
                                                                  && x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₃₄ + 1
                                                                  && a₃₃[i₃₄ := 44][x₁₁] == 44)))
                                                  && (forall x₁₁: int ::
                                                          (exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₃₄ + 1)
                                                          || a₃₃[i₃₄ := 44][x₁₁] == a₃₁[x₁₁])
                                                  && (forall i₁₀: int ::
                                                        (  0 <= i₁₀
                                                          && i₁₀ < i₃₄ + 1
                                                           ==> i₁₀ < 100000)))
                                              &&   i₃₄ < 100000
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
                                                                  && a₃₃[x₁₅] == 45)))
                                                  && (forall x₁₅: int ::
                                                          (exists i₁₄: int ::
                                                                  x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < 0)
                                                          || a₃₃[x₁₅] == a₃₃[x₁₅])
                                                  && (forall i₁₄: int ::
                                                        (  0 <= i₁₄
                                                          && i₁₄ < 0
                                                           ==> i₁₄ < 100000))
                                                  && (forall a₃₅: [int]int, i₃₆: int ::
                                                        (  0 <= i₃₆
                                                          && i₃₆ <= 100000
                                                          && (forall x₁₅: int, i₁₄: int ::
                                                                (  x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < i₃₆
                                                                   ==> (exists i₁₄: int ::
                                                                          i₁₄ < 100000
                                                                          && x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₃₆
                                                                          && a₃₅[x₁₅] == 45)))
                                                          && (forall x₁₅: int ::
                                                                  (exists i₁₄: int ::
                                                                          x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₃₆)
                                                                  || a₃₅[x₁₅] == a₃₃[x₁₅])
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₃₆
                                                                   ==> i₁₄ < 100000))
                                                           ==> (i₃₆ < 100000
                                                               ==> 0 <= i₃₆ + 1
                                                                && i₃₆ + 1 <= 100000
                                                                && (forall x₁₅: int, i₁₄: int ::
                                                                      (  x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₃₆ + 1
                                                                         ==> (exists i₁₄: int ::
                                                                                i₁₄ < 100000
                                                                                && x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₃₆ + 1
                                                                                && a₃₅[i₃₆ := 45][x₁₅] == 45)))
                                                                && (forall x₁₅: int ::
                                                                        (exists i₁₄: int ::
                                                                                x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₃₆ + 1)
                                                                        || a₃₅[i₃₆ := 45][x₁₅] == a₃₃[x₁₅])
                                                                && (forall i₁₄: int ::
                                                                      (  0 <= i₁₄
                                                                        && i₁₄ < i₃₆ + 1
                                                                         ==> i₁₄ < 100000)))
                                                            &&   i₃₆ < 100000
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
                                                                                && a₃₅[x₁₉] == 46)))
                                                                && (forall x₁₉: int ::
                                                                        (exists i₁₈: int ::
                                                                                x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < 0)
                                                                        || a₃₅[x₁₉] == a₃₅[x₁₉])
                                                                && (forall i₁₈: int ::
                                                                      (  0 <= i₁₈
                                                                        && i₁₈ < 0
                                                                         ==> i₁₈ < 100000))
                                                                && (forall a₃₇: [int]int, i₃₈: int ::
                                                                      (  0 <= i₃₈
                                                                        && i₃₈ <= 100000
                                                                        && (forall x₁₉: int, i₁₈: int ::
                                                                              (  x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < i₃₈
                                                                                 ==> (exists i₁₈: int ::
                                                                                        i₁₈ < 100000
                                                                                        && x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < i₃₈
                                                                                        && a₃₇[x₁₉] == 46)))
                                                                        && (forall x₁₉: int ::
                                                                                (exists i₁₈: int ::
                                                                                        x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < i₃₈)
                                                                                || a₃₇[x₁₉] == a₃₅[x₁₉])
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₃₈
                                                                                 ==> i₁₈ < 100000))
                                                                         ==> (i₃₈ < 100000
                                                                             ==> 0 <= i₃₈ + 1
                                                                              && i₃₈ + 1 <= 100000
                                                                              && (forall x₁₉: int, i₁₈: int ::
                                                                                    (  x₁₉ == i₁₈
                                                                                      && 0 <= i₁₈
                                                                                      && i₁₈ < i₃₈ + 1
                                                                                       ==> (exists i₁₈: int ::
                                                                                              i₁₈ < 100000
                                                                                              && x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₃₈ + 1
                                                                                              && a₃₇[i₃₈ := 46][x₁₉] == 46)))
                                                                              && (forall x₁₉: int ::
                                                                                      (exists i₁₈: int ::
                                                                                              x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₃₈ + 1)
                                                                                      || a₃₇[i₃₈ := 46][x₁₉] == a₃₅[x₁₉])
                                                                              && (forall i₁₈: int ::
                                                                                    (  0 <= i₁₈
                                                                                      && i₁₈ < i₃₈ + 1
                                                                                       ==> i₁₈ < 100000)))
                                                                          &&   i₃₈ < 100000
                                                                            ||   0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₂₃: int, i₂₂: int ::
                                                                                    (  x₂₃ == i₂₂
                                                                                      && 0 <= i₂₂
                                                                                      && i₂₂ < 0
                                                                                       ==> (exists i₂₂: int ::
                                                                                              i₂₂ < 100000
                                                                                              && x₂₃ == i₂₂
                                                                                              && 0 <= i₂₂
                                                                                              && i₂₂ < 0
                                                                                              && a₃₇[x₂₃] == 47)))
                                                                              && (forall x₂₃: int ::
                                                                                      (exists i₂₂: int ::
                                                                                              x₂₃ == i₂₂
                                                                                              && 0 <= i₂₂
                                                                                              && i₂₂ < 0)
                                                                                      || a₃₇[x₂₃] == a₃₇[x₂₃])
                                                                              && (forall i₂₂: int ::
                                                                                    (  0 <= i₂₂
                                                                                      && i₂₂ < 0
                                                                                       ==> i₂₂ < 100000))
                                                                              && (forall a₃₉: [int]int, i₄₀: int ::
                                                                                    (  0 <= i₄₀
                                                                                      && i₄₀ <= 100000
                                                                                      && (forall x₂₃: int, i₂₂: int ::
                                                                                            (  x₂₃ == i₂₂
                                                                                              && 0 <= i₂₂
                                                                                              && i₂₂ < i₄₀
                                                                                               ==> (exists i₂₂: int ::
                                                                                                      i₂₂ < 100000
                                                                                                      && x₂₃ == i₂₂
                                                                                                      && 0 <= i₂₂
                                                                                                      && i₂₂ < i₄₀
                                                                                                      && a₃₉[x₂₃] == 47)))
                                                                                      && (forall x₂₃: int ::
                                                                                              (exists i₂₂: int ::
                                                                                                      x₂₃ == i₂₂
                                                                                                      && 0 <= i₂₂
                                                                                                      && i₂₂ < i₄₀)
                                                                                              || a₃₉[x₂₃] == a₃₇[x₂₃])
                                                                                      && (forall i₂₂: int ::
                                                                                            (  0 <= i₂₂
                                                                                              && i₂₂ < i₄₀
                                                                                               ==> i₂₂ < 100000))
                                                                                       ==> (i₄₀ < 100000
                                                                                           ==> 0 <= i₄₀ + 1
                                                                                            && i₄₀ + 1 <= 100000
                                                                                            && (forall x₂₃: int, i₂₂: int ::
                                                                                                  (  x₂₃ == i₂₂
                                                                                                    && 0 <= i₂₂
                                                                                                    && i₂₂ < i₄₀ + 1
                                                                                                     ==> (exists i₂₂: int ::
                                                                                                            i₂₂ < 100000
                                                                                                            && x₂₃ == i₂₂
                                                                                                            && 0 <= i₂₂
                                                                                                            && i₂₂ < i₄₀ + 1
                                                                                                            && a₃₉[i₄₀ := 47][x₂₃] == 47)))
                                                                                            && (forall x₂₃: int ::
                                                                                                    (exists i₂₂: int ::
                                                                                                            x₂₃ == i₂₂
                                                                                                            && 0 <= i₂₂
                                                                                                            && i₂₂ < i₄₀ + 1)
                                                                                                    || a₃₉[i₄₀ := 47][x₂₃] == a₃₇[x₂₃])
                                                                                            && (forall i₂₂: int ::
                                                                                                  (  0 <= i₂₂
                                                                                                    && i₂₂ < i₄₀ + 1
                                                                                                     ==> i₂₂ < 100000)))
                                                                                        &&   i₄₀ < 100000
                                                                                          ||   0 <= 0
                                                                                            && 0 <= 100000
                                                                                            && (forall x₂₇: int ::
                                                                                                  (  0 <= x₂₇
                                                                                                    && x₂₇ < 0
                                                                                                     ==> x₂₇ < 100000))
                                                                                            && (forall x₄₁: int ::
                                                                                                  (  0 <= x₄₁
                                                                                                    && x₄₁ <= 100000
                                                                                                    && (forall x₂₇: int ::
                                                                                                          (  0 <= x₂₇
                                                                                                            && x₂₇ < x₄₁
                                                                                                             ==> x₂₇ < 100000))
                                                                                                     ==> (x₄₁ < 100000
                                                                                                       ==> a₃₉[x₄₁] == 46
                                                                                                        && 0 <= x₄₁ + 1
                                                                                                        && x₄₁ + 1 <= 100000
                                                                                                        && (forall x₂₇: int ::
                                                                                                              (  0 <= x₂₇
                                                                                                                && x₂₇ < x₄₁ + 1
                                                                                                                 ==> x₂₇ < 100000))))))))))))))))));

