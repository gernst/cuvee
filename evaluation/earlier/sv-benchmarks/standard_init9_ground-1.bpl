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
        && (forall a₄₁: [int]int, i₄₂: int ::
              (  0 <= i₄₂
                && i₄₂ <= 100000
                && (forall x₃: int, i₂: int ::
                      (  x₃ == i₂
                        && 0 <= i₂
                        && i₂ < i₄₂
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₄₂
                                && a₄₁[x₃] == 42)))
                && (forall x₃: int ::
                        (exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₄₂)
                        || a₄₁[x₃] == a[x₃])
                && (forall i₂: int ::
                      (  0 <= i₂
                        && i₂ < i₄₂
                         ==> i₂ < 100000))
                 ==> (i₄₂ < 100000
                     ==> 0 <= i₄₂ + 1
                      && i₄₂ + 1 <= 100000
                      && (forall x₃: int, i₂: int ::
                            (  x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₄₂ + 1
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₄₂ + 1
                                      && a₄₁[i₄₂ := 42][x₃] == 42)))
                      && (forall x₃: int ::
                              (exists i₂: int ::
                                      x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₄₂ + 1)
                              || a₄₁[i₄₂ := 42][x₃] == a[x₃])
                      && (forall i₂: int ::
                            (  0 <= i₂
                              && i₂ < i₄₂ + 1
                               ==> i₂ < 100000)))
                  &&   i₄₂ < 100000
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
                                      && a₄₁[x₇] == 43)))
                      && (forall x₇: int ::
                              (exists i₆: int ::
                                      x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < 0)
                              || a₄₁[x₇] == a₄₁[x₇])
                      && (forall i₆: int ::
                            (  0 <= i₆
                              && i₆ < 0
                               ==> i₆ < 100000))
                      && (forall a₄₃: [int]int, i₄₄: int ::
                            (  0 <= i₄₄
                              && i₄₄ <= 100000
                              && (forall x₇: int, i₆: int ::
                                    (  x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < i₄₄
                                       ==> (exists i₆: int ::
                                              i₆ < 100000
                                              && x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₄₄
                                              && a₄₃[x₇] == 43)))
                              && (forall x₇: int ::
                                      (exists i₆: int ::
                                              x₇ == i₆
                                              && 0 <= i₆
                                              && i₆ < i₄₄)
                                      || a₄₃[x₇] == a₄₁[x₇])
                              && (forall i₆: int ::
                                    (  0 <= i₆
                                      && i₆ < i₄₄
                                       ==> i₆ < 100000))
                               ==> (i₄₄ < 100000
                                   ==> 0 <= i₄₄ + 1
                                    && i₄₄ + 1 <= 100000
                                    && (forall x₇: int, i₆: int ::
                                          (  x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₄₄ + 1
                                             ==> (exists i₆: int ::
                                                    i₆ < 100000
                                                    && x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₄₄ + 1
                                                    && a₄₃[i₄₄ := 43][x₇] == 43)))
                                    && (forall x₇: int ::
                                            (exists i₆: int ::
                                                    x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₄₄ + 1)
                                            || a₄₃[i₄₄ := 43][x₇] == a₄₁[x₇])
                                    && (forall i₆: int ::
                                          (  0 <= i₆
                                            && i₆ < i₄₄ + 1
                                             ==> i₆ < 100000)))
                                &&   i₄₄ < 100000
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
                                                    && a₄₃[x₁₁] == 44)))
                                    && (forall x₁₁: int ::
                                            (exists i₁₀: int ::
                                                    x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < 0)
                                            || a₄₃[x₁₁] == a₄₃[x₁₁])
                                    && (forall i₁₀: int ::
                                          (  0 <= i₁₀
                                            && i₁₀ < 0
                                             ==> i₁₀ < 100000))
                                    && (forall a₄₅: [int]int, i₄₆: int ::
                                          (  0 <= i₄₆
                                            && i₄₆ <= 100000
                                            && (forall x₁₁: int, i₁₀: int ::
                                                  (  x₁₁ == i₁₀
                                                    && 0 <= i₁₀
                                                    && i₁₀ < i₄₆
                                                     ==> (exists i₁₀: int ::
                                                            i₁₀ < 100000
                                                            && x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₄₆
                                                            && a₄₅[x₁₁] == 44)))
                                            && (forall x₁₁: int ::
                                                    (exists i₁₀: int ::
                                                            x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₄₆)
                                                    || a₄₅[x₁₁] == a₄₃[x₁₁])
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₄₆
                                                     ==> i₁₀ < 100000))
                                             ==> (i₄₆ < 100000
                                                 ==> 0 <= i₄₆ + 1
                                                  && i₄₆ + 1 <= 100000
                                                  && (forall x₁₁: int, i₁₀: int ::
                                                        (  x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₄₆ + 1
                                                           ==> (exists i₁₀: int ::
                                                                  i₁₀ < 100000
                                                                  && x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₄₆ + 1
                                                                  && a₄₅[i₄₆ := 44][x₁₁] == 44)))
                                                  && (forall x₁₁: int ::
                                                          (exists i₁₀: int ::
                                                                  x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₄₆ + 1)
                                                          || a₄₅[i₄₆ := 44][x₁₁] == a₄₃[x₁₁])
                                                  && (forall i₁₀: int ::
                                                        (  0 <= i₁₀
                                                          && i₁₀ < i₄₆ + 1
                                                           ==> i₁₀ < 100000)))
                                              &&   i₄₆ < 100000
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
                                                                  && a₄₅[x₁₅] == 45)))
                                                  && (forall x₁₅: int ::
                                                          (exists i₁₄: int ::
                                                                  x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < 0)
                                                          || a₄₅[x₁₅] == a₄₅[x₁₅])
                                                  && (forall i₁₄: int ::
                                                        (  0 <= i₁₄
                                                          && i₁₄ < 0
                                                           ==> i₁₄ < 100000))
                                                  && (forall a₄₇: [int]int, i₄₈: int ::
                                                        (  0 <= i₄₈
                                                          && i₄₈ <= 100000
                                                          && (forall x₁₅: int, i₁₄: int ::
                                                                (  x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < i₄₈
                                                                   ==> (exists i₁₄: int ::
                                                                          i₁₄ < 100000
                                                                          && x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₄₈
                                                                          && a₄₇[x₁₅] == 45)))
                                                          && (forall x₁₅: int ::
                                                                  (exists i₁₄: int ::
                                                                          x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₄₈)
                                                                  || a₄₇[x₁₅] == a₄₅[x₁₅])
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₄₈
                                                                   ==> i₁₄ < 100000))
                                                           ==> (i₄₈ < 100000
                                                               ==> 0 <= i₄₈ + 1
                                                                && i₄₈ + 1 <= 100000
                                                                && (forall x₁₅: int, i₁₄: int ::
                                                                      (  x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₄₈ + 1
                                                                         ==> (exists i₁₄: int ::
                                                                                i₁₄ < 100000
                                                                                && x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₄₈ + 1
                                                                                && a₄₇[i₄₈ := 45][x₁₅] == 45)))
                                                                && (forall x₁₅: int ::
                                                                        (exists i₁₄: int ::
                                                                                x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₄₈ + 1)
                                                                        || a₄₇[i₄₈ := 45][x₁₅] == a₄₅[x₁₅])
                                                                && (forall i₁₄: int ::
                                                                      (  0 <= i₁₄
                                                                        && i₁₄ < i₄₈ + 1
                                                                         ==> i₁₄ < 100000)))
                                                            &&   i₄₈ < 100000
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
                                                                                && a₄₇[x₁₉] == 46)))
                                                                && (forall x₁₉: int ::
                                                                        (exists i₁₈: int ::
                                                                                x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < 0)
                                                                        || a₄₇[x₁₉] == a₄₇[x₁₉])
                                                                && (forall i₁₈: int ::
                                                                      (  0 <= i₁₈
                                                                        && i₁₈ < 0
                                                                         ==> i₁₈ < 100000))
                                                                && (forall a₄₉: [int]int, i₅₀: int ::
                                                                      (  0 <= i₅₀
                                                                        && i₅₀ <= 100000
                                                                        && (forall x₁₉: int, i₁₈: int ::
                                                                              (  x₁₉ == i₁₈
                                                                                && 0 <= i₁₈
                                                                                && i₁₈ < i₅₀
                                                                                 ==> (exists i₁₈: int ::
                                                                                        i₁₈ < 100000
                                                                                        && x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < i₅₀
                                                                                        && a₄₉[x₁₉] == 46)))
                                                                        && (forall x₁₉: int ::
                                                                                (exists i₁₈: int ::
                                                                                        x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < i₅₀)
                                                                                || a₄₉[x₁₉] == a₄₇[x₁₉])
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₅₀
                                                                                 ==> i₁₈ < 100000))
                                                                         ==> (i₅₀ < 100000
                                                                             ==> 0 <= i₅₀ + 1
                                                                              && i₅₀ + 1 <= 100000
                                                                              && (forall x₁₉: int, i₁₈: int ::
                                                                                    (  x₁₉ == i₁₈
                                                                                      && 0 <= i₁₈
                                                                                      && i₁₈ < i₅₀ + 1
                                                                                       ==> (exists i₁₈: int ::
                                                                                              i₁₈ < 100000
                                                                                              && x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₅₀ + 1
                                                                                              && a₄₉[i₅₀ := 46][x₁₉] == 46)))
                                                                              && (forall x₁₉: int ::
                                                                                      (exists i₁₈: int ::
                                                                                              x₁₉ == i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₅₀ + 1)
                                                                                      || a₄₉[i₅₀ := 46][x₁₉] == a₄₇[x₁₉])
                                                                              && (forall i₁₈: int ::
                                                                                    (  0 <= i₁₈
                                                                                      && i₁₈ < i₅₀ + 1
                                                                                       ==> i₁₈ < 100000)))
                                                                          &&   i₅₀ < 100000
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
                                                                                              && a₄₉[x₂₃] == 47)))
                                                                              && (forall x₂₃: int ::
                                                                                      (exists i₂₂: int ::
                                                                                              x₂₃ == i₂₂
                                                                                              && 0 <= i₂₂
                                                                                              && i₂₂ < 0)
                                                                                      || a₄₉[x₂₃] == a₄₉[x₂₃])
                                                                              && (forall i₂₂: int ::
                                                                                    (  0 <= i₂₂
                                                                                      && i₂₂ < 0
                                                                                       ==> i₂₂ < 100000))
                                                                              && (forall a₅₁: [int]int, i₅₂: int ::
                                                                                    (  0 <= i₅₂
                                                                                      && i₅₂ <= 100000
                                                                                      && (forall x₂₃: int, i₂₂: int ::
                                                                                            (  x₂₃ == i₂₂
                                                                                              && 0 <= i₂₂
                                                                                              && i₂₂ < i₅₂
                                                                                               ==> (exists i₂₂: int ::
                                                                                                      i₂₂ < 100000
                                                                                                      && x₂₃ == i₂₂
                                                                                                      && 0 <= i₂₂
                                                                                                      && i₂₂ < i₅₂
                                                                                                      && a₅₁[x₂₃] == 47)))
                                                                                      && (forall x₂₃: int ::
                                                                                              (exists i₂₂: int ::
                                                                                                      x₂₃ == i₂₂
                                                                                                      && 0 <= i₂₂
                                                                                                      && i₂₂ < i₅₂)
                                                                                              || a₅₁[x₂₃] == a₄₉[x₂₃])
                                                                                      && (forall i₂₂: int ::
                                                                                            (  0 <= i₂₂
                                                                                              && i₂₂ < i₅₂
                                                                                               ==> i₂₂ < 100000))
                                                                                       ==> (i₅₂ < 100000
                                                                                           ==> 0 <= i₅₂ + 1
                                                                                            && i₅₂ + 1 <= 100000
                                                                                            && (forall x₂₃: int, i₂₂: int ::
                                                                                                  (  x₂₃ == i₂₂
                                                                                                    && 0 <= i₂₂
                                                                                                    && i₂₂ < i₅₂ + 1
                                                                                                     ==> (exists i₂₂: int ::
                                                                                                            i₂₂ < 100000
                                                                                                            && x₂₃ == i₂₂
                                                                                                            && 0 <= i₂₂
                                                                                                            && i₂₂ < i₅₂ + 1
                                                                                                            && a₅₁[i₅₂ := 47][x₂₃] == 47)))
                                                                                            && (forall x₂₃: int ::
                                                                                                    (exists i₂₂: int ::
                                                                                                            x₂₃ == i₂₂
                                                                                                            && 0 <= i₂₂
                                                                                                            && i₂₂ < i₅₂ + 1)
                                                                                                    || a₅₁[i₅₂ := 47][x₂₃] == a₄₉[x₂₃])
                                                                                            && (forall i₂₂: int ::
                                                                                                  (  0 <= i₂₂
                                                                                                    && i₂₂ < i₅₂ + 1
                                                                                                     ==> i₂₂ < 100000)))
                                                                                        &&   i₅₂ < 100000
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
                                                                                                            && a₅₁[x₂₇] == 48)))
                                                                                            && (forall x₂₇: int ::
                                                                                                    (exists i₂₆: int ::
                                                                                                            x₂₇ == i₂₆
                                                                                                            && 0 <= i₂₆
                                                                                                            && i₂₆ < 0)
                                                                                                    || a₅₁[x₂₇] == a₅₁[x₂₇])
                                                                                            && (forall i₂₆: int ::
                                                                                                  (  0 <= i₂₆
                                                                                                    && i₂₆ < 0
                                                                                                     ==> i₂₆ < 100000))
                                                                                            && (forall a₅₃: [int]int, i₅₄: int ::
                                                                                                  (  0 <= i₅₄
                                                                                                    && i₅₄ <= 100000
                                                                                                    && (forall x₂₇: int, i₂₆: int ::
                                                                                                          (  x₂₇ == i₂₆
                                                                                                            && 0 <= i₂₆
                                                                                                            && i₂₆ < i₅₄
                                                                                                             ==> (exists i₂₆: int ::
                                                                                                                    i₂₆ < 100000
                                                                                                                    && x₂₇ == i₂₆
                                                                                                                    && 0 <= i₂₆
                                                                                                                    && i₂₆ < i₅₄
                                                                                                                    && a₅₃[x₂₇] == 48)))
                                                                                                    && (forall x₂₇: int ::
                                                                                                            (exists i₂₆: int ::
                                                                                                                    x₂₇ == i₂₆
                                                                                                                    && 0 <= i₂₆
                                                                                                                    && i₂₆ < i₅₄)
                                                                                                            || a₅₃[x₂₇] == a₅₁[x₂₇])
                                                                                                    && (forall i₂₆: int ::
                                                                                                          (  0 <= i₂₆
                                                                                                            && i₂₆ < i₅₄
                                                                                                             ==> i₂₆ < 100000))
                                                                                                     ==> (i₅₄ < 100000
                                                                                                         ==> 0 <= i₅₄ + 1
                                                                                                          && i₅₄ + 1 <= 100000
                                                                                                          && (forall x₂₇: int, i₂₆: int ::
                                                                                                                (  x₂₇ == i₂₆
                                                                                                                  && 0 <= i₂₆
                                                                                                                  && i₂₆ < i₅₄ + 1
                                                                                                                   ==> (exists i₂₆: int ::
                                                                                                                          i₂₆ < 100000
                                                                                                                          && x₂₇ == i₂₆
                                                                                                                          && 0 <= i₂₆
                                                                                                                          && i₂₆ < i₅₄ + 1
                                                                                                                          && a₅₃[i₅₄ := 48][x₂₇] == 48)))
                                                                                                          && (forall x₂₇: int ::
                                                                                                                  (exists i₂₆: int ::
                                                                                                                          x₂₇ == i₂₆
                                                                                                                          && 0 <= i₂₆
                                                                                                                          && i₂₆ < i₅₄ + 1)
                                                                                                                  || a₅₃[i₅₄ := 48][x₂₇] == a₅₁[x₂₇])
                                                                                                          && (forall i₂₆: int ::
                                                                                                                (  0 <= i₂₆
                                                                                                                  && i₂₆ < i₅₄ + 1
                                                                                                                   ==> i₂₆ < 100000)))
                                                                                                      &&   i₅₄ < 100000
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
                                                                                                                          && a₅₃[x₃₁] == 49)))
                                                                                                          && (forall x₃₁: int ::
                                                                                                                  (exists i₃₀: int ::
                                                                                                                          x₃₁ == i₃₀
                                                                                                                          && 0 <= i₃₀
                                                                                                                          && i₃₀ < 0)
                                                                                                                  || a₅₃[x₃₁] == a₅₃[x₃₁])
                                                                                                          && (forall i₃₀: int ::
                                                                                                                (  0 <= i₃₀
                                                                                                                  && i₃₀ < 0
                                                                                                                   ==> i₃₀ < 100000))
                                                                                                          && (forall a₅₅: [int]int, i₅₆: int ::
                                                                                                                (  0 <= i₅₆
                                                                                                                  && i₅₆ <= 100000
                                                                                                                  && (forall x₃₁: int, i₃₀: int ::
                                                                                                                        (  x₃₁ == i₃₀
                                                                                                                          && 0 <= i₃₀
                                                                                                                          && i₃₀ < i₅₆
                                                                                                                           ==> (exists i₃₀: int ::
                                                                                                                                  i₃₀ < 100000
                                                                                                                                  && x₃₁ == i₃₀
                                                                                                                                  && 0 <= i₃₀
                                                                                                                                  && i₃₀ < i₅₆
                                                                                                                                  && a₅₅[x₃₁] == 49)))
                                                                                                                  && (forall x₃₁: int ::
                                                                                                                          (exists i₃₀: int ::
                                                                                                                                  x₃₁ == i₃₀
                                                                                                                                  && 0 <= i₃₀
                                                                                                                                  && i₃₀ < i₅₆)
                                                                                                                          || a₅₅[x₃₁] == a₅₃[x₃₁])
                                                                                                                  && (forall i₃₀: int ::
                                                                                                                        (  0 <= i₃₀
                                                                                                                          && i₃₀ < i₅₆
                                                                                                                           ==> i₃₀ < 100000))
                                                                                                                   ==> (i₅₆ < 100000
                                                                                                                       ==> 0 <= i₅₆ + 1
                                                                                                                        && i₅₆ + 1 <= 100000
                                                                                                                        && (forall x₃₁: int, i₃₀: int ::
                                                                                                                              (  x₃₁ == i₃₀
                                                                                                                                && 0 <= i₃₀
                                                                                                                                && i₃₀ < i₅₆ + 1
                                                                                                                                 ==> (exists i₃₀: int ::
                                                                                                                                        i₃₀ < 100000
                                                                                                                                        && x₃₁ == i₃₀
                                                                                                                                        && 0 <= i₃₀
                                                                                                                                        && i₃₀ < i₅₆ + 1
                                                                                                                                        && a₅₅[i₅₆ := 49][x₃₁] == 49)))
                                                                                                                        && (forall x₃₁: int ::
                                                                                                                                (exists i₃₀: int ::
                                                                                                                                        x₃₁ == i₃₀
                                                                                                                                        && 0 <= i₃₀
                                                                                                                                        && i₃₀ < i₅₆ + 1)
                                                                                                                                || a₅₅[i₅₆ := 49][x₃₁] == a₅₃[x₃₁])
                                                                                                                        && (forall i₃₀: int ::
                                                                                                                              (  0 <= i₃₀
                                                                                                                                && i₃₀ < i₅₆ + 1
                                                                                                                                 ==> i₃₀ < 100000)))
                                                                                                                    &&   i₅₆ < 100000
                                                                                                                      ||   0 <= 0
                                                                                                                        && 0 <= 100000
                                                                                                                        && (forall x₃₅: int, i₃₄: int ::
                                                                                                                              (  x₃₅ == i₃₄
                                                                                                                                && 0 <= i₃₄
                                                                                                                                && i₃₄ < 0
                                                                                                                                 ==> (exists i₃₄: int ::
                                                                                                                                        i₃₄ < 100000
                                                                                                                                        && x₃₅ == i₃₄
                                                                                                                                        && 0 <= i₃₄
                                                                                                                                        && i₃₄ < 0
                                                                                                                                        && a₅₅[x₃₅] == 50)))
                                                                                                                        && (forall x₃₅: int ::
                                                                                                                                (exists i₃₄: int ::
                                                                                                                                        x₃₅ == i₃₄
                                                                                                                                        && 0 <= i₃₄
                                                                                                                                        && i₃₄ < 0)
                                                                                                                                || a₅₅[x₃₅] == a₅₅[x₃₅])
                                                                                                                        && (forall i₃₄: int ::
                                                                                                                              (  0 <= i₃₄
                                                                                                                                && i₃₄ < 0
                                                                                                                                 ==> i₃₄ < 100000))
                                                                                                                        && (forall a₅₇: [int]int, i₅₈: int ::
                                                                                                                              (  0 <= i₅₈
                                                                                                                                && i₅₈ <= 100000
                                                                                                                                && (forall x₃₅: int, i₃₄: int ::
                                                                                                                                      (  x₃₅ == i₃₄
                                                                                                                                        && 0 <= i₃₄
                                                                                                                                        && i₃₄ < i₅₈
                                                                                                                                         ==> (exists i₃₄: int ::
                                                                                                                                                i₃₄ < 100000
                                                                                                                                                && x₃₅ == i₃₄
                                                                                                                                                && 0 <= i₃₄
                                                                                                                                                && i₃₄ < i₅₈
                                                                                                                                                && a₅₇[x₃₅] == 50)))
                                                                                                                                && (forall x₃₅: int ::
                                                                                                                                        (exists i₃₄: int ::
                                                                                                                                                x₃₅ == i₃₄
                                                                                                                                                && 0 <= i₃₄
                                                                                                                                                && i₃₄ < i₅₈)
                                                                                                                                        || a₅₇[x₃₅] == a₅₅[x₃₅])
                                                                                                                                && (forall i₃₄: int ::
                                                                                                                                      (  0 <= i₃₄
                                                                                                                                        && i₃₄ < i₅₈
                                                                                                                                         ==> i₃₄ < 100000))
                                                                                                                                 ==> (i₅₈ < 100000
                                                                                                                                     ==> 0 <= i₅₈ + 1
                                                                                                                                      && i₅₈ + 1 <= 100000
                                                                                                                                      && (forall x₃₅: int, i₃₄: int ::
                                                                                                                                            (  x₃₅ == i₃₄
                                                                                                                                              && 0 <= i₃₄
                                                                                                                                              && i₃₄ < i₅₈ + 1
                                                                                                                                               ==> (exists i₃₄: int ::
                                                                                                                                                      i₃₄ < 100000
                                                                                                                                                      && x₃₅ == i₃₄
                                                                                                                                                      && 0 <= i₃₄
                                                                                                                                                      && i₃₄ < i₅₈ + 1
                                                                                                                                                      && a₅₇[i₅₈ := 50][x₃₅] == 50)))
                                                                                                                                      && (forall x₃₅: int ::
                                                                                                                                              (exists i₃₄: int ::
                                                                                                                                                      x₃₅ == i₃₄
                                                                                                                                                      && 0 <= i₃₄
                                                                                                                                                      && i₃₄ < i₅₈ + 1)
                                                                                                                                              || a₅₇[i₅₈ := 50][x₃₅] == a₅₅[x₃₅])
                                                                                                                                      && (forall i₃₄: int ::
                                                                                                                                            (  0 <= i₃₄
                                                                                                                                              && i₃₄ < i₅₈ + 1
                                                                                                                                               ==> i₃₄ < 100000)))
                                                                                                                                  &&   i₅₈ < 100000
                                                                                                                                    ||   0 <= 0
                                                                                                                                      && 0 <= 100000
                                                                                                                                      && (forall x₃₉: int ::
                                                                                                                                            (  0 <= x₃₉
                                                                                                                                              && x₃₉ < 0
                                                                                                                                               ==> x₃₉ < 100000))
                                                                                                                                      && (forall x₅₉: int ::
                                                                                                                                            (  0 <= x₅₉
                                                                                                                                              && x₅₉ <= 100000
                                                                                                                                              && (forall x₃₉: int ::
                                                                                                                                                    (  0 <= x₃₉
                                                                                                                                                      && x₃₉ < x₅₉
                                                                                                                                                       ==> x₃₉ < 100000))
                                                                                                                                               ==> (x₅₉ < 100000
                                                                                                                                                 ==> a₅₇[x₅₉] == 49
                                                                                                                                                  && 0 <= x₅₉ + 1
                                                                                                                                                  && x₅₉ + 1 <= 100000
                                                                                                                                                  && (forall x₃₉: int ::
                                                                                                                                                        (  0 <= x₃₉
                                                                                                                                                          && x₃₉ < x₅₉ + 1
                                                                                                                                                           ==> x₃₉ < 100000))))))))))))))))))))))));

