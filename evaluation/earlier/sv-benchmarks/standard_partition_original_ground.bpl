data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, bb: [int]int, cc: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < 0
                 ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                        i₅ < 100000
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < 0
                        && aa[x₆] == __VERIFIER_nondet_int₁₄)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < 0)
                || aa[x₆] == aa[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < 0
                 ==> i₅ < 100000))
        && (forall aa₂₄: [int]int, i₂₅: int ::
              (  0 <= i₂₅
                && i₂₅ <= 100000
                && (forall x₆: int, i₅: int ::
                      (  x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅
                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                i₅ < 100000
                                && x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₂₅
                                && aa₂₄[x₆] == __VERIFIER_nondet_int₁₄)))
                && (forall x₆: int ::
                        (exists i₅: int ::
                                x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₂₅)
                        || aa₂₄[x₆] == aa[x₆])
                && (forall i₅: int ::
                      (  0 <= i₅
                        && i₅ < i₂₅
                         ==> i₅ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₂₅ < 100000
                           ==> 0 <= i₂₅ + 1
                            && i₂₅ + 1 <= 100000
                            && (forall x₆: int, i₅: int ::
                                  (  x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₅ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                            i₅ < 100000
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₂₅ + 1
                                            && aa₂₄[i₂₅ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₆: int ::
                                    (exists i₅: int ::
                                            x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₂₅ + 1)
                                    || aa₂₄[i₂₅ := __VERIFIER_nondet_int₁][x₆] == aa[x₆])
                            && (forall i₅: int ::
                                  (  0 <= i₅
                                    && i₅ < i₂₅ + 1
                                     ==> i₅ < 100000))))
                  &&   i₂₅ < 100000
                    ||   0 <= 0
                      && 0 <= 0
                      && 0 <= 0
                      && 0 <= 100000
                      && (forall x₁₂: int, c₉: int ::
                            (  x₁₂ == c₉
                              && 0 <= c₉
                              && c₉ < 0
                               ==> (exists a₁₀: int ::
                                    (0 <= aa₂₄[a₁₀]
                                       ==> false))))
                      && (forall x₁₂: int ::
                              (exists c₉: int ::
                                      x₁₂ == c₉
                                      && 0 <= c₉
                                      && c₉ < 0)
                              || cc[x₁₂] == cc[x₁₂])
                      && (forall x₁₃: int, b₁₁: int ::
                            (  x₁₃ == b₁₁
                              && 0 <= b₁₁
                              && b₁₁ < 0
                               ==> (exists a₁₀: int, b₁₁: int ::
                                      0 <= aa₂₄[a₁₀]
                                      && a₁₀ < 100000
                                      && x₁₃ == b₁₁
                                      && 0 <= b₁₁
                                      && b₁₁ < 0
                                      && bb[x₁₃] == aa₂₄[a₁₀])))
                      && (forall x₁₃: int ::
                              (exists b₁₁: int ::
                                      x₁₃ == b₁₁
                                      && 0 <= b₁₁
                                      && b₁₁ < 0)
                              || bb[x₁₃] == bb[x₁₃])
                      && (forall c₉: int, a₁₀: int, b₁₁: int ::
                            (  0 <= c₉
                              && 0 <= a₁₀
                              && 0 <= b₁₁
                              && c₉ < 0
                              && a₁₀ < 0
                              && b₁₁ < 0
                               ==> a₁₀ < 100000))
                      && (forall c₂₆: int, cc₂₇: [int]int, a₂₈: int, b₂₉: int, bb₃₀: [int]int ::
                            (  0 <= c₂₆
                              && 0 <= a₂₈
                              && 0 <= b₂₉
                              && a₂₈ <= 100000
                              && (forall x₁₂: int, c₉: int ::
                                    (  x₁₂ == c₉
                                      && 0 <= c₉
                                      && c₉ < c₂₆
                                       ==> (exists a₁₀: int ::
                                            (0 <= aa₂₄[a₁₀]
                                               ==> false))))
                              && (forall x₁₂: int ::
                                      (exists c₉: int ::
                                              x₁₂ == c₉
                                              && 0 <= c₉
                                              && c₉ < c₂₆)
                                      || cc₂₇[x₁₂] == cc[x₁₂])
                              && (forall x₁₃: int, b₁₁: int ::
                                    (  x₁₃ == b₁₁
                                      && 0 <= b₁₁
                                      && b₁₁ < b₂₉
                                       ==> (exists a₁₀: int, b₁₁: int ::
                                              0 <= aa₂₄[a₁₀]
                                              && a₁₀ < 100000
                                              && x₁₃ == b₁₁
                                              && 0 <= b₁₁
                                              && b₁₁ < b₂₉
                                              && bb₃₀[x₁₃] == aa₂₄[a₁₀])))
                              && (forall x₁₃: int ::
                                      (exists b₁₁: int ::
                                              x₁₃ == b₁₁
                                              && 0 <= b₁₁
                                              && b₁₁ < b₂₉)
                                      || bb₃₀[x₁₃] == bb[x₁₃])
                              && (forall c₉: int, a₁₀: int, b₁₁: int ::
                                    (  0 <= c₉
                                      && 0 <= a₁₀
                                      && 0 <= b₁₁
                                      && c₉ < c₂₆
                                      && a₁₀ < a₂₈
                                      && b₁₁ < b₂₉
                                       ==> a₁₀ < 100000))
                               ==> (a₂₈ < 100000
                                   ==> (0 <= aa₂₄[a₂₈]
                                       ==> 0 <= c₂₆
                                        && 0 <= a₂₈ + 1
                                        && 0 <= b₂₉ + 1
                                        && a₂₈ + 1 <= 100000
                                        && (forall x₁₂: int, c₉: int ::
                                              (  x₁₂ == c₉
                                                && 0 <= c₉
                                                && c₉ < c₂₆
                                                 ==> (exists a₁₀: int ::
                                                      (0 <= aa₂₄[a₁₀]
                                                         ==> false))))
                                        && (forall x₁₂: int ::
                                                (exists c₉: int ::
                                                        x₁₂ == c₉
                                                        && 0 <= c₉
                                                        && c₉ < c₂₆)
                                                || cc₂₇[x₁₂] == cc[x₁₂])
                                        && (forall x₁₃: int, b₁₁: int ::
                                              (  x₁₃ == b₁₁
                                                && 0 <= b₁₁
                                                && b₁₁ < b₂₉ + 1
                                                 ==> (exists a₁₀: int, b₁₁: int ::
                                                        0 <= aa₂₄[a₁₀]
                                                        && a₁₀ < 100000
                                                        && x₁₃ == b₁₁
                                                        && 0 <= b₁₁
                                                        && b₁₁ < b₂₉ + 1
                                                        && bb₃₀[b₂₉ := aa₂₄[a₂₈]][x₁₃] == aa₂₄[a₁₀])))
                                        && (forall x₁₃: int ::
                                                (exists b₁₁: int ::
                                                        x₁₃ == b₁₁
                                                        && 0 <= b₁₁
                                                        && b₁₁ < b₂₉ + 1)
                                                || bb₃₀[b₂₉ := aa₂₄[a₂₈]][x₁₃] == bb[x₁₃])
                                        && (forall c₉: int, a₁₀: int, b₁₁: int ::
                                              (  0 <= c₉
                                                && 0 <= a₁₀
                                                && 0 <= b₁₁
                                                && c₉ < c₂₆
                                                && a₁₀ < a₂₈ + 1
                                                && b₁₁ < b₂₉ + 1
                                                 ==> a₁₀ < 100000)))
                                    &&   0 <= aa₂₄[a₂₈]
                                      ||   0 <= c₂₆ + 1
                                        && 0 <= a₂₈ + 1
                                        && 0 <= b₂₉
                                        && a₂₈ + 1 <= 100000
                                        && (forall x₁₂: int, c₉: int ::
                                              (  x₁₂ == c₉
                                                && 0 <= c₉
                                                && c₉ < c₂₆ + 1
                                                 ==> (exists a₁₀: int ::
                                                      (0 <= aa₂₄[a₁₀]
                                                         ==> false))))
                                        && (forall x₁₂: int ::
                                                (exists c₉: int ::
                                                        x₁₂ == c₉
                                                        && 0 <= c₉
                                                        && c₉ < c₂₆ + 1)
                                                || cc₂₇[c₂₆ := aa₂₄[a₂₈]][x₁₂] == cc[x₁₂])
                                        && (forall x₁₃: int, b₁₁: int ::
                                              (  x₁₃ == b₁₁
                                                && 0 <= b₁₁
                                                && b₁₁ < b₂₉
                                                 ==> (exists a₁₀: int, b₁₁: int ::
                                                        0 <= aa₂₄[a₁₀]
                                                        && a₁₀ < 100000
                                                        && x₁₃ == b₁₁
                                                        && 0 <= b₁₁
                                                        && b₁₁ < b₂₉
                                                        && bb₃₀[x₁₃] == aa₂₄[a₁₀])))
                                        && (forall x₁₃: int ::
                                                (exists b₁₁: int ::
                                                        x₁₃ == b₁₁
                                                        && 0 <= b₁₁
                                                        && b₁₁ < b₂₉)
                                                || bb₃₀[x₁₃] == bb[x₁₃])
                                        && (forall c₉: int, a₁₀: int, b₁₁: int ::
                                              (  0 <= c₉
                                                && 0 <= a₁₀
                                                && 0 <= b₁₁
                                                && c₉ < c₂₆ + 1
                                                && a₁₀ < a₂₈ + 1
                                                && b₁₁ < b₂₉
                                                 ==> a₁₀ < 100000)))
                                &&   a₂₈ < 100000
                                  ||   0 <= 0
                                    && 0 <= b₂₉
                                    && (forall x₂₀: int ::
                                          (  0 <= x₂₀
                                            && x₂₀ < 0
                                             ==> x₂₀ < b₂₉))
                                    && (forall x₃₁: int ::
                                          (  0 <= x₃₁
                                            && x₃₁ <= b₂₉
                                            && (forall x₂₀: int ::
                                                  (  0 <= x₂₀
                                                    && x₂₀ < x₃₁
                                                     ==> x₂₀ < b₂₉))
                                             ==> (x₃₁ < b₂₉
                                                 ==> 0 <= bb₃₀[x₃₁]
                                                  && 0 <= x₃₁ + 1
                                                  && x₃₁ + 1 <= b₂₉
                                                  && (forall x₂₀: int ::
                                                        (  0 <= x₂₀
                                                          && x₂₀ < x₃₁ + 1
                                                           ==> x₂₀ < b₂₉)))
                                              &&   x₃₁ < b₂₉
                                                ||   0 <= 0
                                                  && 0 <= c₂₆
                                                  && (forall x₂₂: int ::
                                                        (  0 <= x₂₂
                                                          && x₂₂ < 0
                                                           ==> x₂₂ < c₂₆))
                                                  && (forall x₃₂: int ::
                                                        (  0 <= x₃₂
                                                          && x₃₂ <= c₂₆
                                                          && (forall x₂₂: int ::
                                                                (  0 <= x₂₂
                                                                  && x₂₂ < x₃₂
                                                                   ==> x₂₂ < c₂₆))
                                                           ==> (x₃₂ < c₂₆
                                                             ==> cc₂₇[x₃₂] < 0
                                                              && 0 <= x₃₂ + 1
                                                              && x₃₂ + 1 <= c₂₆
                                                              && (forall x₂₂: int ::
                                                                    (  0 <= x₂₂
                                                                      && x₂₂ < x₃₂ + 1
                                                                       ==> x₂₂ < c₂₆))))))))))));

