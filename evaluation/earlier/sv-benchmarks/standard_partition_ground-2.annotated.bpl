data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int ::
      (forall bb: [int]int ::
            (forall cc: [int]int ::
                    true
                    && 0 <= 0
                    && 0 <= 100000
                    && (forall x₆: int ::
                          ((exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                             ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                    i₅ < 100000
                                    && x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < 0
                                    && aa[x₆] == __VERIFIER_nondet_int₁₄)))
                    && (forall x₆: int ::
                          (!((exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                          )
                             ==> aa[x₆] == aa[x₆]))
                    && (forall i₅: int ::
                          (  i₅ <= i₅
                            && 0 <= i₅
                            && i₅ < 0
                             ==> i₅ < 100000))
                    && (forall aa₂₄: [int]int, i₂₅: int ::
                          (  true
                            && 0 <= i₂₅
                            && i₂₅ <= 100000
                            && (forall x₆: int ::
                                  ((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₅)
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                            i₅ < 100000
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₂₅
                                            && aa₂₄[x₆] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₆: int ::
                                  (!((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₅)
                                  )
                                     ==> aa₂₄[x₆] == aa[x₆]))
                            && (forall i₅: int ::
                                  (  i₅ <= i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₅
                                     ==> i₅ < 100000))
                             ==> (i₂₅ < 100000
                                 ==> (forall __VERIFIER_nondet_int₁: int ::
                                        true
                                        && 0 <= i₂₅ + 1
                                        && i₂₅ + 1 <= 100000
                                        && (forall x₆: int ::
                                              ((exists i₅: int ::
                                                      x₆ == i₅
                                                      && 0 <= i₅
                                                      && i₅ < i₂₅ + 1)
                                                 ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                        i₅ < 100000
                                                        && x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₂₅ + 1
                                                        && aa₂₄[i₂₅ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)))
                                        && (forall x₆: int ::
                                              (!((exists i₅: int ::
                                                      x₆ == i₅
                                                      && 0 <= i₅
                                                      && i₅ < i₂₅ + 1)
                                              )
                                                 ==> aa₂₄[i₂₅ := __VERIFIER_nondet_int₁][x₆] == aa[x₆]))
                                        && (forall i₅: int ::
                                              (  i₅ <= i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₅ + 1
                                                 ==> i₅ < 100000))
                                        && true
                                        && (true
                                           ==> true)))
                              && (!(i₂₅ < 100000
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= 0
                                      && 0 <= 100000
                                      && (forall x₁₁: int ::
                                            ((exists b₉: int ::
                                                    x₁₁ == b₉
                                                    && 0 <= b₉
                                                    && b₉ < 0)
                                               ==> (exists b₉: int, a₁₀: int ::
                                                      0 <= aa₂₄[a₁₀]
                                                      && a₁₀ < 100000
                                                      && x₁₁ == b₉
                                                      && 0 <= b₉
                                                      && b₉ < 0
                                                      && bb[x₁₁] == aa₂₄[a₁₀])))
                                      && (forall x₁₁: int ::
                                            (!((exists b₉: int ::
                                                    x₁₁ == b₉
                                                    && 0 <= b₉
                                                    && b₉ < 0)
                                            )
                                               ==> bb[x₁₁] == bb[x₁₁]))
                                      && (forall b₉: int, a₁₀: int ::
                                            (  b₉ <= b₉
                                              && a₁₀ <= a₁₀
                                              && 0 <= b₉
                                              && b₉ < 0
                                              && 0 <= a₁₀
                                              && a₁₀ < 0
                                               ==> a₁₀ < 100000))
                                      && (forall bb₂₆: [int]int, b₂₇: int, a₂₈: int ::
                                            (  true
                                              && 0 <= b₂₇
                                              && 0 <= a₂₈
                                              && a₂₈ <= 100000
                                              && (forall x₁₁: int ::
                                                    ((exists b₉: int ::
                                                            x₁₁ == b₉
                                                            && 0 <= b₉
                                                            && b₉ < b₂₇)
                                                       ==> (exists b₉: int, a₁₀: int ::
                                                              0 <= aa₂₄[a₁₀]
                                                              && a₁₀ < 100000
                                                              && x₁₁ == b₉
                                                              && 0 <= b₉
                                                              && b₉ < b₂₇
                                                              && bb₂₆[x₁₁] == aa₂₄[a₁₀])))
                                              && (forall x₁₁: int ::
                                                    (!((exists b₉: int ::
                                                            x₁₁ == b₉
                                                            && 0 <= b₉
                                                            && b₉ < b₂₇)
                                                    )
                                                       ==> bb₂₆[x₁₁] == bb[x₁₁]))
                                              && (forall b₉: int, a₁₀: int ::
                                                    (  b₉ <= b₉
                                                      && a₁₀ <= a₁₀
                                                      && 0 <= b₉
                                                      && b₉ < b₂₇
                                                      && 0 <= a₁₀
                                                      && a₁₀ < a₂₈
                                                       ==> a₁₀ < 100000))
                                               ==> (a₂₈ < 100000
                                                   ==> (0 <= aa₂₄[a₂₈]
                                                       ==> true
                                                        && 0 <= b₂₇ + 1
                                                        && 0 <= a₂₈ + 1
                                                        && a₂₈ + 1 <= 100000
                                                        && (forall x₁₁: int ::
                                                              ((exists b₉: int ::
                                                                      x₁₁ == b₉
                                                                      && 0 <= b₉
                                                                      && b₉ < b₂₇ + 1)
                                                                 ==> (exists b₉: int, a₁₀: int ::
                                                                        0 <= aa₂₄[a₁₀]
                                                                        && a₁₀ < 100000
                                                                        && x₁₁ == b₉
                                                                        && 0 <= b₉
                                                                        && b₉ < b₂₇ + 1
                                                                        && bb₂₆[b₂₇ := aa₂₄[a₂₈]][x₁₁] == aa₂₄[a₁₀])))
                                                        && (forall x₁₁: int ::
                                                              (!((exists b₉: int ::
                                                                      x₁₁ == b₉
                                                                      && 0 <= b₉
                                                                      && b₉ < b₂₇ + 1)
                                                              )
                                                                 ==> bb₂₆[b₂₇ := aa₂₄[a₂₈]][x₁₁] == bb[x₁₁]))
                                                        && (forall b₉: int, a₁₀: int ::
                                                              (  b₉ <= b₉
                                                                && a₁₀ <= a₁₀
                                                                && 0 <= b₉
                                                                && b₉ < b₂₇ + 1
                                                                && 0 <= a₁₀
                                                                && a₁₀ < a₂₈ + 1
                                                                 ==> a₁₀ < 100000))
                                                        && true
                                                        && (true
                                                           ==> true))
                                                    && (!(0 <= aa₂₄[a₂₈]
                                                    )
                                                       ==> true
                                                        && 0 <= b₂₇
                                                        && 0 <= a₂₈ + 1
                                                        && a₂₈ + 1 <= 100000
                                                        && (forall x₁₁: int ::
                                                              ((exists b₉: int ::
                                                                      x₁₁ == b₉
                                                                      && 0 <= b₉
                                                                      && b₉ < b₂₇)
                                                                 ==> (exists b₉: int, a₁₀: int ::
                                                                        0 <= aa₂₄[a₁₀]
                                                                        && a₁₀ < 100000
                                                                        && x₁₁ == b₉
                                                                        && 0 <= b₉
                                                                        && b₉ < b₂₇
                                                                        && bb₂₆[x₁₁] == aa₂₄[a₁₀])))
                                                        && (forall x₁₁: int ::
                                                              (!((exists b₉: int ::
                                                                      x₁₁ == b₉
                                                                      && 0 <= b₉
                                                                      && b₉ < b₂₇)
                                                              )
                                                                 ==> bb₂₆[x₁₁] == bb[x₁₁]))
                                                        && (forall b₉: int, a₁₀: int ::
                                                              (  b₉ <= b₉
                                                                && a₁₀ <= a₁₀
                                                                && 0 <= b₉
                                                                && b₉ < b₂₇
                                                                && 0 <= a₁₀
                                                                && a₁₀ < a₂₈ + 1
                                                                 ==> a₁₀ < 100000))
                                                        && true
                                                        && (true
                                                           ==> true)))
                                                && (!(a₂₈ < 100000
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 0 <= 0
                                                        && 0 <= 0
                                                        && 0 <= 100000
                                                        && (forall x₁₇: int ::
                                                              ((exists c₁₅: int ::
                                                                      x₁₇ == c₁₅
                                                                      && 0 <= c₁₅
                                                                      && c₁₅ < 0)
                                                                 ==> (exists c₁₅: int, a₁₆: int ::
                                                                        aa₂₄[a₁₆] < 0
                                                                        && a₁₆ < 100000
                                                                        && x₁₇ == c₁₅
                                                                        && 0 <= c₁₅
                                                                        && c₁₅ < 0
                                                                        && cc[x₁₇] == aa₂₄[a₁₆])))
                                                        && (forall x₁₇: int ::
                                                              (!((exists c₁₅: int ::
                                                                      x₁₇ == c₁₅
                                                                      && 0 <= c₁₅
                                                                      && c₁₅ < 0)
                                                              )
                                                                 ==> cc[x₁₇] == cc[x₁₇]))
                                                        && (forall c₁₅: int, a₁₆: int ::
                                                              (  c₁₅ <= c₁₅
                                                                && a₁₆ <= a₁₆
                                                                && 0 <= c₁₅
                                                                && c₁₅ < 0
                                                                && 0 <= a₁₆
                                                                && a₁₆ < 0
                                                                 ==> a₁₆ < 100000))
                                                        && (forall cc₂₉: [int]int, c₃₀: int, a₃₁: int ::
                                                              (  true
                                                                && 0 <= c₃₀
                                                                && 0 <= a₃₁
                                                                && a₃₁ <= 100000
                                                                && (forall x₁₇: int ::
                                                                      ((exists c₁₅: int ::
                                                                              x₁₇ == c₁₅
                                                                              && 0 <= c₁₅
                                                                              && c₁₅ < c₃₀)
                                                                         ==> (exists c₁₅: int, a₁₆: int ::
                                                                                aa₂₄[a₁₆] < 0
                                                                                && a₁₆ < 100000
                                                                                && x₁₇ == c₁₅
                                                                                && 0 <= c₁₅
                                                                                && c₁₅ < c₃₀
                                                                                && cc₂₉[x₁₇] == aa₂₄[a₁₆])))
                                                                && (forall x₁₇: int ::
                                                                      (!((exists c₁₅: int ::
                                                                              x₁₇ == c₁₅
                                                                              && 0 <= c₁₅
                                                                              && c₁₅ < c₃₀)
                                                                      )
                                                                         ==> cc₂₉[x₁₇] == cc[x₁₇]))
                                                                && (forall c₁₅: int, a₁₆: int ::
                                                                      (  c₁₅ <= c₁₅
                                                                        && a₁₆ <= a₁₆
                                                                        && 0 <= c₁₅
                                                                        && c₁₅ < c₃₀
                                                                        && 0 <= a₁₆
                                                                        && a₁₆ < a₃₁
                                                                         ==> a₁₆ < 100000))
                                                                 ==> (a₃₁ < 100000
                                                                     ==> (aa₂₄[a₃₁] < 0
                                                                         ==> true
                                                                          && 0 <= c₃₀ + 1
                                                                          && 0 <= a₃₁ + 1
                                                                          && a₃₁ + 1 <= 100000
                                                                          && (forall x₁₇: int ::
                                                                                ((exists c₁₅: int ::
                                                                                        x₁₇ == c₁₅
                                                                                        && 0 <= c₁₅
                                                                                        && c₁₅ < c₃₀ + 1)
                                                                                   ==> (exists c₁₅: int, a₁₆: int ::
                                                                                          aa₂₄[a₁₆] < 0
                                                                                          && a₁₆ < 100000
                                                                                          && x₁₇ == c₁₅
                                                                                          && 0 <= c₁₅
                                                                                          && c₁₅ < c₃₀ + 1
                                                                                          && cc₂₉[c₃₀ := aa₂₄[a₃₁]][x₁₇] == aa₂₄[a₁₆])))
                                                                          && (forall x₁₇: int ::
                                                                                (!((exists c₁₅: int ::
                                                                                        x₁₇ == c₁₅
                                                                                        && 0 <= c₁₅
                                                                                        && c₁₅ < c₃₀ + 1)
                                                                                )
                                                                                   ==> cc₂₉[c₃₀ := aa₂₄[a₃₁]][x₁₇] == cc[x₁₇]))
                                                                          && (forall c₁₅: int, a₁₆: int ::
                                                                                (  c₁₅ <= c₁₅
                                                                                  && a₁₆ <= a₁₆
                                                                                  && 0 <= c₁₅
                                                                                  && c₁₅ < c₃₀ + 1
                                                                                  && 0 <= a₁₆
                                                                                  && a₁₆ < a₃₁ + 1
                                                                                   ==> a₁₆ < 100000))
                                                                          && true
                                                                          && (true
                                                                             ==> true))
                                                                      && (!(aa₂₄[a₃₁] < 0
                                                                      )
                                                                         ==> true
                                                                          && 0 <= c₃₀
                                                                          && 0 <= a₃₁ + 1
                                                                          && a₃₁ + 1 <= 100000
                                                                          && (forall x₁₇: int ::
                                                                                ((exists c₁₅: int ::
                                                                                        x₁₇ == c₁₅
                                                                                        && 0 <= c₁₅
                                                                                        && c₁₅ < c₃₀)
                                                                                   ==> (exists c₁₅: int, a₁₆: int ::
                                                                                          aa₂₄[a₁₆] < 0
                                                                                          && a₁₆ < 100000
                                                                                          && x₁₇ == c₁₅
                                                                                          && 0 <= c₁₅
                                                                                          && c₁₅ < c₃₀
                                                                                          && cc₂₉[x₁₇] == aa₂₄[a₁₆])))
                                                                          && (forall x₁₇: int ::
                                                                                (!((exists c₁₅: int ::
                                                                                        x₁₇ == c₁₅
                                                                                        && 0 <= c₁₅
                                                                                        && c₁₅ < c₃₀)
                                                                                )
                                                                                   ==> cc₂₉[x₁₇] == cc[x₁₇]))
                                                                          && (forall c₁₅: int, a₁₆: int ::
                                                                                (  c₁₅ <= c₁₅
                                                                                  && a₁₆ <= a₁₆
                                                                                  && 0 <= c₁₅
                                                                                  && c₁₅ < c₃₀
                                                                                  && 0 <= a₁₆
                                                                                  && a₁₆ < a₃₁ + 1
                                                                                   ==> a₁₆ < 100000))
                                                                          && true
                                                                          && (true
                                                                             ==> true)))
                                                                  && (!(a₃₁ < 100000
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= 0
                                                                          && 0 <= b₂₇
                                                                          && (forall x₂₂: int ::
                                                                                (  x₂₂ <= x₂₂
                                                                                  && 0 <= x₂₂
                                                                                  && x₂₂ < 0
                                                                                   ==> x₂₂ < b₂₇))
                                                                          && (forall x₃₂: int ::
                                                                                (  true
                                                                                  && 0 <= x₃₂
                                                                                  && x₃₂ <= b₂₇
                                                                                  && (forall x₂₂: int ::
                                                                                        (  x₂₂ <= x₂₂
                                                                                          && 0 <= x₂₂
                                                                                          && x₂₂ < x₃₂
                                                                                           ==> x₂₂ < b₂₇))
                                                                                   ==> (x₃₂ < b₂₇
                                                                                       ==> 0 <= bb₂₆[x₃₂]
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= x₃₂ + 1
                                                                                            && x₃₂ + 1 <= b₂₇
                                                                                            && (forall x₂₂: int ::
                                                                                                  (  x₂₂ <= x₂₂
                                                                                                    && 0 <= x₂₂
                                                                                                    && x₂₂ < x₃₂ + 1
                                                                                                     ==> x₂₂ < b₂₇))
                                                                                            && true
                                                                                            && (true
                                                                                               ==> true)))
                                                                                    && (!(x₃₂ < b₂₇
                                                                                    )
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true)))))))))))))))))));

