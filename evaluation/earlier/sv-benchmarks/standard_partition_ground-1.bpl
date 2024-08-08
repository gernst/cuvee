data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, bb: [int]int, cc: [int]int ::
        0 <= 0
        && 0 <= 0
        && 0 <= 100000
        && (forall x₇: int, a₆: int ::
              (  x₇ == a₆
                && 0 <= a₆
                && a₆ < 0
                 ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                          0 <= aa[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                          && a₆ < 100000
                          && x₇ == a₆
                          && 0 <= a₆
                          && a₆ < 0
                          && aa[x₇] == __VERIFIER_nondet_int₁₄)
                  || (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                        (0 <= aa[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                           ==> false))))
        && (forall x₇: int ::
                (exists a₆: int ::
                        x₇ == a₆
                        && 0 <= a₆
                        && a₆ < 0)
                || aa[x₇] == aa[x₇])
        && (forall x₈: int, b₅: int ::
              (  x₈ == b₅
                && 0 <= b₅
                && b₅ < 0
                 ==> (exists __VERIFIER_nondet_int₁₄: int, b₅: int, a₆: int ::
                        0 <= aa[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                        && a₆ < 100000
                        && x₈ == b₅
                        && 0 <= b₅
                        && b₅ < 0
                        && bb[x₈] == aa[a₆ := __VERIFIER_nondet_int₁₄][a₆])))
        && (forall x₈: int ::
                (exists b₅: int ::
                        x₈ == b₅
                        && 0 <= b₅
                        && b₅ < 0)
                || bb[x₈] == bb[x₈])
        && (forall b₅: int, a₆: int ::
              (  0 <= b₅
                && 0 <= a₆
                && b₅ < 0
                && a₆ < 0
                 ==> a₆ < 100000))
        && (forall aa₂₄: [int]int, bb₂₅: [int]int, b₂₆: int, a₂₇: int ::
              (  0 <= b₂₆
                && 0 <= a₂₇
                && a₂₇ <= 100000
                && (forall x₇: int, a₆: int ::
                      (  x₇ == a₆
                        && 0 <= a₆
                        && a₆ < a₂₇
                         ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                                  0 <= aa₂₄[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                  && a₆ < 100000
                                  && x₇ == a₆
                                  && 0 <= a₆
                                  && a₆ < a₂₇
                                  && aa₂₄[x₇] == __VERIFIER_nondet_int₁₄)
                          || (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                                (0 <= aa₂₄[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                   ==> false))))
                && (forall x₇: int ::
                        (exists a₆: int ::
                                x₇ == a₆
                                && 0 <= a₆
                                && a₆ < a₂₇)
                        || aa₂₄[x₇] == aa[x₇])
                && (forall x₈: int, b₅: int ::
                      (  x₈ == b₅
                        && 0 <= b₅
                        && b₅ < b₂₆
                         ==> (exists __VERIFIER_nondet_int₁₄: int, b₅: int, a₆: int ::
                                0 <= aa₂₄[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                && a₆ < 100000
                                && x₈ == b₅
                                && 0 <= b₅
                                && b₅ < b₂₆
                                && bb₂₅[x₈] == aa₂₄[a₆ := __VERIFIER_nondet_int₁₄][a₆])))
                && (forall x₈: int ::
                        (exists b₅: int ::
                                x₈ == b₅
                                && 0 <= b₅
                                && b₅ < b₂₆)
                        || bb₂₅[x₈] == bb[x₈])
                && (forall b₅: int, a₆: int ::
                      (  0 <= b₅
                        && 0 <= a₆
                        && b₅ < b₂₆
                        && a₆ < a₂₇
                         ==> a₆ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (a₂₇ < 100000
                           ==> (0 <= aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₂₇]
                               ==> 0 <= b₂₆ + 1
                                && 0 <= a₂₇ + 1
                                && a₂₇ + 1 <= 100000
                                && (forall x₇: int, a₆: int ::
                                      (  x₇ == a₆
                                        && 0 <= a₆
                                        && a₆ < a₂₇ + 1
                                         ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                                                  0 <= aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                                  && a₆ < 100000
                                                  && x₇ == a₆
                                                  && 0 <= a₆
                                                  && a₆ < a₂₇ + 1
                                                  && aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][x₇] == __VERIFIER_nondet_int₁₄)
                                          || (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                                                (0 <= aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                                   ==> false))))
                                && (forall x₇: int ::
                                        (exists a₆: int ::
                                                x₇ == a₆
                                                && 0 <= a₆
                                                && a₆ < a₂₇ + 1)
                                        || aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][x₇] == aa[x₇])
                                && (forall x₈: int, b₅: int ::
                                      (  x₈ == b₅
                                        && 0 <= b₅
                                        && b₅ < b₂₆ + 1
                                         ==> (exists __VERIFIER_nondet_int₁₄: int, b₅: int, a₆: int ::
                                                0 <= aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                                && a₆ < 100000
                                                && x₈ == b₅
                                                && 0 <= b₅
                                                && b₅ < b₂₆ + 1
                                                && bb₂₅[b₂₆ := aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₂₇]][x₈] == aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₆ := __VERIFIER_nondet_int₁₄][a₆])))
                                && (forall x₈: int ::
                                        (exists b₅: int ::
                                                x₈ == b₅
                                                && 0 <= b₅
                                                && b₅ < b₂₆ + 1)
                                        || bb₂₅[b₂₆ := aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₂₇]][x₈] == bb[x₈])
                                && (forall b₅: int, a₆: int ::
                                      (  0 <= b₅
                                        && 0 <= a₆
                                        && b₅ < b₂₆ + 1
                                        && a₆ < a₂₇ + 1
                                         ==> a₆ < 100000)))
                            &&   0 <= aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₂₇]
                              ||   0 <= b₂₆
                                && 0 <= a₂₇ + 1
                                && a₂₇ + 1 <= 100000
                                && (forall x₇: int, a₆: int ::
                                      (  x₇ == a₆
                                        && 0 <= a₆
                                        && a₆ < a₂₇ + 1
                                         ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                                                  0 <= aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                                  && a₆ < 100000
                                                  && x₇ == a₆
                                                  && 0 <= a₆
                                                  && a₆ < a₂₇ + 1
                                                  && aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][x₇] == __VERIFIER_nondet_int₁₄)
                                          || (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                                                (0 <= aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                                   ==> false))))
                                && (forall x₇: int ::
                                        (exists a₆: int ::
                                                x₇ == a₆
                                                && 0 <= a₆
                                                && a₆ < a₂₇ + 1)
                                        || aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][x₇] == aa[x₇])
                                && (forall x₈: int, b₅: int ::
                                      (  x₈ == b₅
                                        && 0 <= b₅
                                        && b₅ < b₂₆
                                         ==> (exists __VERIFIER_nondet_int₁₄: int, b₅: int, a₆: int ::
                                                0 <= aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₆ := __VERIFIER_nondet_int₁₄][a₆]
                                                && a₆ < 100000
                                                && x₈ == b₅
                                                && 0 <= b₅
                                                && b₅ < b₂₆
                                                && bb₂₅[x₈] == aa₂₄[a₂₇ := __VERIFIER_nondet_int₁][a₆ := __VERIFIER_nondet_int₁₄][a₆])))
                                && (forall x₈: int ::
                                        (exists b₅: int ::
                                                x₈ == b₅
                                                && 0 <= b₅
                                                && b₅ < b₂₆)
                                        || bb₂₅[x₈] == bb[x₈])
                                && (forall b₅: int, a₆: int ::
                                      (  0 <= b₅
                                        && 0 <= a₆
                                        && b₅ < b₂₆
                                        && a₆ < a₂₇ + 1
                                         ==> a₆ < 100000))))
                  &&   a₂₇ < 100000
                    ||   0 <= 0
                      && 0 <= 0
                      && 0 <= 100000
                      && (forall x₁₅: int, c₁₃: int ::
                            (  x₁₅ == c₁₃
                              && 0 <= c₁₃
                              && c₁₃ < 0
                               ==> (exists c₁₃: int, a₁₄: int ::
                                      0 <= aa₂₄[a₁₄]
                                      && a₁₄ < 100000
                                      && x₁₅ == c₁₃
                                      && 0 <= c₁₃
                                      && c₁₃ < 0
                                      && cc[x₁₅] == aa₂₄[a₁₄])))
                      && (forall x₁₅: int ::
                              (exists c₁₃: int ::
                                      x₁₅ == c₁₃
                                      && 0 <= c₁₃
                                      && c₁₃ < 0)
                              || cc[x₁₅] == cc[x₁₅])
                      && (forall c₁₃: int, a₁₄: int ::
                            (  0 <= c₁₃
                              && 0 <= a₁₄
                              && c₁₃ < 0
                              && a₁₄ < 0
                               ==> a₁₄ < 100000))
                      && (forall cc₂₈: [int]int, c₂₉: int, a₃₀: int ::
                            (  0 <= c₂₉
                              && 0 <= a₃₀
                              && a₃₀ <= 100000
                              && (forall x₁₅: int, c₁₃: int ::
                                    (  x₁₅ == c₁₃
                                      && 0 <= c₁₃
                                      && c₁₃ < c₂₉
                                       ==> (exists c₁₃: int, a₁₄: int ::
                                              0 <= aa₂₄[a₁₄]
                                              && a₁₄ < 100000
                                              && x₁₅ == c₁₃
                                              && 0 <= c₁₃
                                              && c₁₃ < c₂₉
                                              && cc₂₈[x₁₅] == aa₂₄[a₁₄])))
                              && (forall x₁₅: int ::
                                      (exists c₁₃: int ::
                                              x₁₅ == c₁₃
                                              && 0 <= c₁₃
                                              && c₁₃ < c₂₉)
                                      || cc₂₈[x₁₅] == cc[x₁₅])
                              && (forall c₁₃: int, a₁₄: int ::
                                    (  0 <= c₁₃
                                      && 0 <= a₁₄
                                      && c₁₃ < c₂₉
                                      && a₁₄ < a₃₀
                                       ==> a₁₄ < 100000))
                               ==> (a₃₀ < 100000
                                   ==> (0 <= aa₂₄[a₃₀]
                                       ==> 0 <= c₂₉ + 1
                                        && 0 <= a₃₀ + 1
                                        && a₃₀ + 1 <= 100000
                                        && (forall x₁₅: int, c₁₃: int ::
                                              (  x₁₅ == c₁₃
                                                && 0 <= c₁₃
                                                && c₁₃ < c₂₉ + 1
                                                 ==> (exists c₁₃: int, a₁₄: int ::
                                                        0 <= aa₂₄[a₁₄]
                                                        && a₁₄ < 100000
                                                        && x₁₅ == c₁₃
                                                        && 0 <= c₁₃
                                                        && c₁₃ < c₂₉ + 1
                                                        && cc₂₈[c₂₉ := aa₂₄[a₃₀]][x₁₅] == aa₂₄[a₁₄])))
                                        && (forall x₁₅: int ::
                                                (exists c₁₃: int ::
                                                        x₁₅ == c₁₃
                                                        && 0 <= c₁₃
                                                        && c₁₃ < c₂₉ + 1)
                                                || cc₂₈[c₂₉ := aa₂₄[a₃₀]][x₁₅] == cc[x₁₅])
                                        && (forall c₁₃: int, a₁₄: int ::
                                              (  0 <= c₁₃
                                                && 0 <= a₁₄
                                                && c₁₃ < c₂₉ + 1
                                                && a₁₄ < a₃₀ + 1
                                                 ==> a₁₄ < 100000)))
                                    &&   0 <= aa₂₄[a₃₀]
                                      ||   0 <= c₂₉
                                        && 0 <= a₃₀ + 1
                                        && a₃₀ + 1 <= 100000
                                        && (forall x₁₅: int, c₁₃: int ::
                                              (  x₁₅ == c₁₃
                                                && 0 <= c₁₃
                                                && c₁₃ < c₂₉
                                                 ==> (exists c₁₃: int, a₁₄: int ::
                                                        0 <= aa₂₄[a₁₄]
                                                        && a₁₄ < 100000
                                                        && x₁₅ == c₁₃
                                                        && 0 <= c₁₃
                                                        && c₁₃ < c₂₉
                                                        && cc₂₈[x₁₅] == aa₂₄[a₁₄])))
                                        && (forall x₁₅: int ::
                                                (exists c₁₃: int ::
                                                        x₁₅ == c₁₃
                                                        && 0 <= c₁₃
                                                        && c₁₃ < c₂₉)
                                                || cc₂₈[x₁₅] == cc[x₁₅])
                                        && (forall c₁₃: int, a₁₄: int ::
                                              (  0 <= c₁₃
                                                && 0 <= a₁₄
                                                && c₁₃ < c₂₉
                                                && a₁₄ < a₃₀ + 1
                                                 ==> a₁₄ < 100000)))
                                &&   a₃₀ < 100000
                                  ||   0 <= 0
                                    && 0 <= b₂₆
                                    && (forall x₂₀: int ::
                                          (  0 <= x₂₀
                                            && x₂₀ < 0
                                             ==> x₂₀ < b₂₆))
                                    && (forall x₃₁: int ::
                                          (  0 <= x₃₁
                                            && x₃₁ <= b₂₆
                                            && (forall x₂₀: int ::
                                                  (  0 <= x₂₀
                                                    && x₂₀ < x₃₁
                                                     ==> x₂₀ < b₂₆))
                                             ==> (x₃₁ < b₂₆
                                                 ==> 0 <= bb₂₅[x₃₁]
                                                  && 0 <= x₃₁ + 1
                                                  && x₃₁ + 1 <= b₂₆
                                                  && (forall x₂₀: int ::
                                                        (  0 <= x₂₀
                                                          && x₂₀ < x₃₁ + 1
                                                           ==> x₂₀ < b₂₆)))
                                              &&   x₃₁ < b₂₆
                                                ||   0 <= 0
                                                  && 0 <= c₂₉
                                                  && (forall x₂₂: int ::
                                                        (  0 <= x₂₂
                                                          && x₂₂ < 0
                                                           ==> x₂₂ < c₂₉))
                                                  && (forall x₃₂: int ::
                                                        (  0 <= x₃₂
                                                          && x₃₂ <= c₂₉
                                                          && (forall x₂₂: int ::
                                                                (  0 <= x₂₂
                                                                  && x₂₂ < x₃₂
                                                                   ==> x₂₂ < c₂₉))
                                                           ==> (x₃₂ < c₂₉
                                                             ==> cc₂₈[x₃₂] < 0
                                                              && 0 <= x₃₂ + 1
                                                              && x₃₂ + 1 <= c₂₉
                                                              && (forall x₂₂: int ::
                                                                    (  0 <= x₂₂
                                                                      && x₂₂ < x₃₂ + 1
                                                                       ==> x₂₂ < c₂₉))))))))))));

