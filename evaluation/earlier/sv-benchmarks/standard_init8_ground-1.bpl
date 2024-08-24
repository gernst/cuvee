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
        && (forall a₃₇: [int]int, i₃₈: int ::
              (  0 <= i₃₈
                && i₃₈ <= 100000
                && (forall x₃: int, i₂: int ::
                      (  x₃ == i₂
                        && 0 <= i₂
                        && i₂ < i₃₈
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₃₈
                                && a₃₇[x₃] == 42)))
                && (forall x₃: int ::
                        (exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₃₈)
                        || a₃₇[x₃] == a[x₃])
                && (forall i₂: int ::
                      (  0 <= i₂
                        && i₂ < i₃₈
                         ==> i₂ < 100000))
                 ==> (i₃₈ < 100000
                     ==> 0 <= i₃₈ + 1
                      && i₃₈ + 1 <= 100000
                      && (forall x₃: int, i₂: int ::
                            (  x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₃₈ + 1
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₃₈ + 1
                                      && a₃₇[i₃₈ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                              (exists i₂: int ::
                                      x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₃₈ + 1)
                              || a₃₇[i₃₈ := 42][x₃] == a[x₃])
                      && (forall i₂: int ::
                            (  0 <= i₂
                              && i₂ < i₃₈ + 1
                               ==> i₂ < 100000)))
                  &&   i₃₈ < 100000
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
                                      && a₃₇[x₇] == 43)))
                      && (forall x₇: int ::
                              (exists i₆: int ::
                                      x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < 0)
                              || a₃₇[x₇] == a₃₇[x₇])
                      && (forall i₆: int ::
                            (  0 <= i₆
                              && i₆ < 0
                               ==> i₆ < 100000))
                      && (forall a₃₉: [int]int, i₄₀: int ::
                            (  0 <= i₄₀
                              && i₄₀ <= 100000
                              && (forall x₇: int, i₆: int ::
                                    (  x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < i₄₀
                                       ==> (exists i₆: int ::
                                              i₆ < 100000
                                              && x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₄₀
                                              && a₃₉[x₇] == 43)))
                              && (forall x₇: int ::
                                      (exists i₆: int ::
                                              x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₄₀)
                                      || a₃₉[x₇] == a₃₇[x₇])
                              && (forall i₆: int ::
                                    (  0 <= i₆
                                      && i₆ < i₄₀
                                       ==> i₆ < 100000))
                               ==> (i₄₀ < 100000
                                   ==> 0 <= i₄₀ + 1
                                    && i₄₀ + 1 <= 100000
                                    && (forall x₇: int, i₆: int ::
                                          (  x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₄₀ + 1
                                             ==> (exists i₆: int ::
                                                    i₆ < 100000
                                                    && x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₄₀ + 1
                                                    && a₃₉[i₄₀ := 43][x₇] == 43)))
                                    && (forall x₇: int ::
                                            (exists i₆: int ::
                                                    x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₄₀ + 1)
                                            || a₃₉[i₄₀ := 43][x₇] == a₃₇[x₇])
                                    && (forall i₆: int ::
                                          (  0 <= i₆
                                            && i₆ < i₄₀ + 1
                                             ==> i₆ < 100000)))
                                &&   i₄₀ < 100000
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
                                                    && a₃₉[x₁₁] == 44)))
                                    && (forall x₁₁: int ::
                                            (exists i₁₀: int ::
                                                    x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < 0)
                                            || a₃₉[x₁₁] == a₃₉[x₁₁])
                                    && (forall i₁₀: int ::
                                          (  0 <= i₁₀
                                            && i₁₀ < 0
                                             ==> i₁₀ < 100000))
                                    && (forall a₄₁: [int]int, i₄₂: int ::
                                          (  0 <= i₄₂
                                            && i₄₂ <= 100000
                                            && (forall x₁₁: int, i₁₀: int ::
                                                  (  x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < i₄₂
                                                     ==> (exists i₁₀: int ::
                                                            i₁₀ < 100000
                                                            && x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₄₂
                                                            && a₄₁[x₁₁] == 44)))
                                            && (forall x₁₁: int ::
                                                    (exists i₁₀: int ::
                                                            x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₄₂)
                                                    || a₄₁[x₁₁] == a₃₉[x₁₁])
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₄₂
                                                     ==> i₁₀ < 100000))
                                             ==> (i₄₂ < 100000
                                                 ==> 0 <= i₄₂ + 1
                                                  && i₄₂ + 1 <= 100000
                                                  && (forall x₁₁: int, i₁₀: int ::
                                                        (  x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₄₂ + 1
                                                           ==> (exists i₁₀: int ::
                                                                  i₁₀ < 100000
                                                                  && x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₄₂ + 1
                                                                  && a₄₁[i₄₂ := 44][x₁₁] == 44)))
                                                  && (forall x₁₁: int ::
                                                          (exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₄₂ + 1)
                                                          || a₄₁[i₄₂ := 44][x₁₁] == a₃₉[x₁₁])
                                                  && (forall i₁₀: int ::
                                                        (  0 <= i₁₀
                                                          && i₁₀ < i₄₂ + 1
                                                           ==> i₁₀ < 100000)))
                                              &&   i₄₂ < 100000
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
                                                                  && a₄₁[x₁₅] == 45)))
                                                  && (forall x₁₅: int ::
                                                          (exists i₁₄: int ::
                                                                  x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < 0)
                                                          || a₄₁[x₁₅] == a₄₁[x₁₅])
                                                  && (forall i₁₄: int ::
                                                        (  0 <= i₁₄
                                                          && i₁₄ < 0
                                                           ==> i₁₄ < 100000))
                                                  && (forall a₄₃: [int]int, i₄₄: int ::
                                                        (  0 <= i₄₄
                                                          && i₄₄ <= 100000
                                                          && (forall x₁₅: int, i₁₄: int ::
                                                                (  x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < i₄₄
                                                                   ==> (exists i₁₄: int ::
                                                                          i₁₄ < 100000
                                                                          && x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₄₄
                                                                          && a₄₃[x₁₅] == 45)))
                                                          && (forall x₁₅: int ::
                                                                  (exists i₁₄: int ::
                                                                          x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₄₄)
                                                                  || a₄₃[x₁₅] == a₄₁[x₁₅])
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₄₄
                                                                   ==> i₁₄ < 100000))
                                                           ==> (i₄₄ < 100000
                                                               ==> 0 <= i₄₄ + 1
                                                                && i₄₄ + 1 <= 100000
                                                                && (forall x₁₅: int, i₁₄: int ::
                                                                      (  x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₄₄ + 1
                                                                         ==> (exists i₁₄: int ::
                                                                                i₁₄ < 100000
                                                                                && x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₄₄ + 1
                                                                                && a₄₃[i₄₄ := 45][x₁₅] == 45)))
                                                                && (forall x₁₅: int ::
                                                                        (exists i₁₄: int ::
                                                                                x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₄₄ + 1)
                                                                        || a₄₃[i₄₄ := 45][x₁₅] == a₄₁[x₁₅])
                                                                && (forall i₁₄: int ::
                                                                      (  0 <= i₁₄
                                                                        && i₁₄ < i₄₄ + 1
                                                                         ==> i₁₄ < 100000)))
                                                            &&   i₄₄ < 100000
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
                                                                                && a₄₃[x₁₉] == 46)))
                                                                && (forall x₁₉: int ::
                                                                        (exists i₁₈: int ::
                                                                                x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < 0)
                                                                        || a₄₃[x₁₉] == a₄₃[x₁₉])
                                                                && (forall i₁₈: int ::
                                                                      (  0 <= i₁₈
                                                                        && i₁₈ < 0
                                                                         ==> i₁₈ < 100000))
                                                                && (forall a₄₅: [int]int, i₄₆: int ::
                                                                      (  0 <= i₄₆
                                                                        && i₄₆ <= 100000
                                                                        && (forall x₁₉: int, i₁₈: int ::
                                                                              (  x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < i₄₆
                                                                                 ==> (exists i₁₈: int ::
                                                                                        i₁₈ < 100000
                                                                                        && x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < i₄₆
                                                                                        && a₄₅[x₁₉] == 46)))
                                                                        && (forall x₁₉: int ::
                                                                                (exists i₁₈: int ::
                                                                                        x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < i₄₆)
                                                                                || a₄₅[x₁₉] == a₄₃[x₁₉])
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₄₆
                                                                                 ==> i₁₈ < 100000))
                                                                         ==> (i₄₆ < 100000
                                                                             ==> 0 <= i₄₆ + 1
                                                                              && i₄₆ + 1 <= 100000
                                                                              && (forall x₁₉: int, i₁₈: int ::
                                                                                    (  x₁₉ == i₁₈
                                                                                      && 0 <= i₁₈
                                                                                      && i₁₈ < i₄₆ + 1
                                                                                       ==> (exists i₁₈: int ::
                                                                                              i₁₈ < 100000
                                                                                              && x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₄₆ + 1
                                                                                              && a₄₅[i₄₆ := 46][x₁₉] == 46)))
                                                                              && (forall x₁₉: int ::
                                                                                      (exists i₁₈: int ::
                                                                                              x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₄₆ + 1)
                                                                                      || a₄₅[i₄₆ := 46][x₁₉] == a₄₃[x₁₉])
                                                                              && (forall i₁₈: int ::
                                                                                    (  0 <= i₁₈
                                                                                      && i₁₈ < i₄₆ + 1
                                                                                       ==> i₁₈ < 100000)))
                                                                          &&   i₄₆ < 100000
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
                                                                                              && a₄₅[x₂₃] == 47)))
                                                                              && (forall x₂₃: int ::
                                                                                      (exists i₂₂: int ::
                                                                                              x₂₃ == i₂₂
                                                                                              && 0 <= i₂₂
                                                                                              && i₂₂ < 0)
                                                                                      || a₄₅[x₂₃] == a₄₅[x₂₃])
                                                                              && (forall i₂₂: int ::
                                                                                    (  0 <= i₂₂
                                                                                      && i₂₂ < 0
                                                                                       ==> i₂₂ < 100000))
                                                                              && (forall a₄₇: [int]int, i₄₈: int ::
                                                                                    (  0 <= i₄₈
                                                                                      && i₄₈ <= 100000
                                                                                      && (forall x₂₃: int, i₂₂: int ::
                                                                                            (  x₂₃ == i₂₂
                                                                                              && 0 <= i₂₂
                                                                                              && i₂₂ < i₄₈
                                                                                               ==> (exists i₂₂: int ::
                                                                                                      i₂₂ < 100000
                                                                                                      && x₂₃ == i₂₂
                                                                                                      && 0 <= i₂₂
                                                                                                      && i₂₂ < i₄₈
                                                                                                      && a₄₇[x₂₃] == 47)))
                                                                                      && (forall x₂₃: int ::
                                                                                              (exists i₂₂: int ::
                                                                                                      x₂₃ == i₂₂
                                                                                                      && 0 <= i₂₂
                                                                                                      && i₂₂ < i₄₈)
                                                                                              || a₄₇[x₂₃] == a₄₅[x₂₃])
                                                                                      && (forall i₂₂: int ::
                                                                                            (  0 <= i₂₂
                                                                                              && i₂₂ < i₄₈
                                                                                               ==> i₂₂ < 100000))
                                                                                       ==> (i₄₈ < 100000
                                                                                           ==> 0 <= i₄₈ + 1
                                                                                            && i₄₈ + 1 <= 100000
                                                                                            && (forall x₂₃: int, i₂₂: int ::
                                                                                                  (  x₂₃ == i₂₂
                                                                                                    && 0 <= i₂₂
                                                                                                    && i₂₂ < i₄₈ + 1
                                                                                                     ==> (exists i₂₂: int ::
                                                                                                            i₂₂ < 100000
                                                                                                            && x₂₃ == i₂₂
                                                                                                            && 0 <= i₂₂
                                                                                                            && i₂₂ < i₄₈ + 1
                                                                                                            && a₄₇[i₄₈ := 47][x₂₃] == 47)))
                                                                                            && (forall x₂₃: int ::
                                                                                                    (exists i₂₂: int ::
                                                                                                            x₂₃ == i₂₂
                                                                                                            && 0 <= i₂₂
                                                                                                            && i₂₂ < i₄₈ + 1)
                                                                                                    || a₄₇[i₄₈ := 47][x₂₃] == a₄₅[x₂₃])
                                                                                            && (forall i₂₂: int ::
                                                                                                  (  0 <= i₂₂
                                                                                                    && i₂₂ < i₄₈ + 1
                                                                                                     ==> i₂₂ < 100000)))
                                                                                        &&   i₄₈ < 100000
                                                                                          ||   0 <= 0
                                                                                            && 0 <= 100000
                                                                                            && (forall x₂₇: int, i₂₆: int ::
                                                                                                  (  x₂₇ == i₂₆
                                                                                                    && 0 <= i₂₆
                                                                                                    && i₂₆ < 0
                                                                                                     ==> (exists i₂₆: int ::
                                                                                                            i₂₆ < 100000
                                                                                                            && x₂₇ == i₂₆
                                                                                                            && 0 <= i₂₆
                                                                                                            && i₂₆ < 0
                                                                                                            && a₄₇[x₂₇] == 48)))
                                                                                            && (forall x₂₇: int ::
                                                                                                    (exists i₂₆: int ::
                                                                                                            x₂₇ == i₂₆
                                                                                                            && 0 <= i₂₆
                                                                                                            && i₂₆ < 0)
                                                                                                    || a₄₇[x₂₇] == a₄₇[x₂₇])
                                                                                            && (forall i₂₆: int ::
                                                                                                  (  0 <= i₂₆
                                                                                                    && i₂₆ < 0
                                                                                                     ==> i₂₆ < 100000))
                                                                                            && (forall a₄₉: [int]int, i₅₀: int ::
                                                                                                  (  0 <= i₅₀
                                                                                                    && i₅₀ <= 100000
                                                                                                    && (forall x₂₇: int, i₂₆: int ::
                                                                                                          (  x₂₇ == i₂₆
                                                                                                            && 0 <= i₂₆
                                                                                                            && i₂₆ < i₅₀
                                                                                                             ==> (exists i₂₆: int ::
                                                                                                                    i₂₆ < 100000
                                                                                                                    && x₂₇ == i₂₆
                                                                                                                    && 0 <= i₂₆
                                                                                                                    && i₂₆ < i₅₀
                                                                                                                    && a₄₉[x₂₇] == 48)))
                                                                                                    && (forall x₂₇: int ::
                                                                                                            (exists i₂₆: int ::
                                                                                                                    x₂₇ == i₂₆
                                                                                                                    && 0 <= i₂₆
                                                                                                                    && i₂₆ < i₅₀)
                                                                                                            || a₄₉[x₂₇] == a₄₇[x₂₇])
                                                                                                    && (forall i₂₆: int ::
                                                                                                          (  0 <= i₂₆
                                                                                                            && i₂₆ < i₅₀
                                                                                                             ==> i₂₆ < 100000))
                                                                                                     ==> (i₅₀ < 100000
                                                                                                         ==> 0 <= i₅₀ + 1
                                                                                                          && i₅₀ + 1 <= 100000
                                                                                                          && (forall x₂₇: int, i₂₆: int ::
                                                                                                                (  x₂₇ == i₂₆
                                                                                                                  && 0 <= i₂₆
                                                                                                                  && i₂₆ < i₅₀ + 1
                                                                                                                   ==> (exists i₂₆: int ::
                                                                                                                          i₂₆ < 100000
                                                                                                                          && x₂₇ == i₂₆
                                                                                                                          && 0 <= i₂₆
                                                                                                                          && i₂₆ < i₅₀ + 1
                                                                                                                          && a₄₉[i₅₀ := 48][x₂₇] == 48)))
                                                                                                          && (forall x₂₇: int ::
                                                                                                                  (exists i₂₆: int ::
                                                                                                                          x₂₇ == i₂₆
                                                                                                                          && 0 <= i₂₆
                                                                                                                          && i₂₆ < i₅₀ + 1)
                                                                                                                  || a₄₉[i₅₀ := 48][x₂₇] == a₄₇[x₂₇])
                                                                                                          && (forall i₂₆: int ::
                                                                                                                (  0 <= i₂₆
                                                                                                                  && i₂₆ < i₅₀ + 1
                                                                                                                   ==> i₂₆ < 100000)))
                                                                                                      &&   i₅₀ < 100000
                                                                                                        ||   0 <= 0
                                                                                                          && 0 <= 100000
                                                                                                          && (forall x₃₁: int, i₃₀: int ::
                                                                                                                (  x₃₁ == i₃₀
                                                                                                                  && 0 <= i₃₀
                                                                                                                  && i₃₀ < 0
                                                                                                                   ==> (exists i₃₀: int ::
                                                                                                                          i₃₀ < 100000
                                                                                                                          && x₃₁ == i₃₀
                                                                                                                          && 0 <= i₃₀
                                                                                                                          && i₃₀ < 0
                                                                                                                          && a₄₉[x₃₁] == 49)))
                                                                                                          && (forall x₃₁: int ::
                                                                                                                  (exists i₃₀: int ::
                                                                                                                          x₃₁ == i₃₀
                                                                                                                          && 0 <= i₃₀
                                                                                                                          && i₃₀ < 0)
                                                                                                                  || a₄₉[x₃₁] == a₄₉[x₃₁])
                                                                                                          && (forall i₃₀: int ::
                                                                                                                (  0 <= i₃₀
                                                                                                                  && i₃₀ < 0
                                                                                                                   ==> i₃₀ < 100000))
                                                                                                          && (forall a₅₁: [int]int, i₅₂: int ::
                                                                                                                (  0 <= i₅₂
                                                                                                                  && i₅₂ <= 100000
                                                                                                                  && (forall x₃₁: int, i₃₀: int ::
                                                                                                                        (  x₃₁ == i₃₀
                                                                                                                          && 0 <= i₃₀
                                                                                                                          && i₃₀ < i₅₂
                                                                                                                           ==> (exists i₃₀: int ::
                                                                                                                                  i₃₀ < 100000
                                                                                                                                  && x₃₁ == i₃₀
                                                                                                                                  && 0 <= i₃₀
                                                                                                                                  && i₃₀ < i₅₂
                                                                                                                                  && a₅₁[x₃₁] == 49)))
                                                                                                                  && (forall x₃₁: int ::
                                                                                                                          (exists i₃₀: int ::
                                                                                                                                  x₃₁ == i₃₀
                                                                                                                                  && 0 <= i₃₀
                                                                                                                                  && i₃₀ < i₅₂)
                                                                                                                          || a₅₁[x₃₁] == a₄₉[x₃₁])
                                                                                                                  && (forall i₃₀: int ::
                                                                                                                        (  0 <= i₃₀
                                                                                                                          && i₃₀ < i₅₂
                                                                                                                           ==> i₃₀ < 100000))
                                                                                                                   ==> (i₅₂ < 100000
                                                                                                                       ==> 0 <= i₅₂ + 1
                                                                                                                        && i₅₂ + 1 <= 100000
                                                                                                                        && (forall x₃₁: int, i₃₀: int ::
                                                                                                                              (  x₃₁ == i₃₀
                                                                                                                                && 0 <= i₃₀
                                                                                                                                && i₃₀ < i₅₂ + 1
                                                                                                                                 ==> (exists i₃₀: int ::
                                                                                                                                        i₃₀ < 100000
                                                                                                                                        && x₃₁ == i₃₀
                                                                                                                                        && 0 <= i₃₀
                                                                                                                                        && i₃₀ < i₅₂ + 1
                                                                                                                                        && a₅₁[i₅₂ := 49][x₃₁] == 49)))
                                                                                                                        && (forall x₃₁: int ::
                                                                                                                                (exists i₃₀: int ::
                                                                                                                                        x₃₁ == i₃₀
                                                                                                                                        && 0 <= i₃₀
                                                                                                                                        && i₃₀ < i₅₂ + 1)
                                                                                                                                || a₅₁[i₅₂ := 49][x₃₁] == a₄₉[x₃₁])
                                                                                                                        && (forall i₃₀: int ::
                                                                                                                              (  0 <= i₃₀
                                                                                                                                && i₃₀ < i₅₂ + 1
                                                                                                                                 ==> i₃₀ < 100000)))
                                                                                                                    &&   i₅₂ < 100000
                                                                                                                      ||   0 <= 0
                                                                                                                        && 0 <= 100000
                                                                                                                        && (forall x₃₅: int ::
                                                                                                                              (  0 <= x₃₅
                                                                                                                                && x₃₅ < 0
                                                                                                                                 ==> x₃₅ < 100000))
                                                                                                                        && (forall x₅₃: int ::
                                                                                                                              (  0 <= x₅₃
                                                                                                                                && x₅₃ <= 100000
                                                                                                                                && (forall x₃₅: int ::
                                                                                                                                      (  0 <= x₃₅
                                                                                                                                        && x₃₅ < x₅₃
                                                                                                                                         ==> x₃₅ < 100000))
                                                                                                                                 ==> (x₅₃ < 100000
                                                                                                                                   ==> a₅₁[x₅₃] == 48
                                                                                                                                    && 0 <= x₅₃ + 1
                                                                                                                                    && x₅₃ + 1 <= 100000
                                                                                                                                    && (forall x₃₅: int ::
                                                                                                                                          (  0 <= x₃₅
                                                                                                                                            && x₃₅ < x₅₃ + 1
                                                                                                                                             ==> x₃₅ < 100000))))))))))))))))))))));

