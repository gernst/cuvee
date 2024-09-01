data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall b: [int]int ::
            (forall c: [int]int ::
                    true
                    && 0 <= 0
                    && 0 <= 100000
                    && (forall x₇: int ::
                          ((exists j₆: int ::
                                  x₇ == j₆
                                  && 0 <= j₆
                                  && j₆ < 0)
                             ==> (exists __VERIFIER_nondet_int₁₄: int, j₆: int ::
                                    j₆ < 100000
                                    && x₇ == j₆
                                    && 0 <= j₆
                                    && j₆ < 0
                                    && a[x₇] == __VERIFIER_nondet_int₁₄)))
                    && (forall x₇: int ::
                          (!((exists j₆: int ::
                                  x₇ == j₆
                                  && 0 <= j₆
                                  && j₆ < 0)
                          )
                             ==> a[x₇] == a[x₇]))
                    && (forall x₈: int ::
                          ((exists j₆: int ::
                                  x₈ == j₆
                                  && 0 <= j₆
                                  && j₆ < 0)
                             ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                                    j₆ < 100000
                                    && x₈ == j₆
                                    && 0 <= j₆
                                    && j₆ < 0
                                    && b[x₈] == __VERIFIER_nondet_int₂₅)))
                    && (forall x₈: int ::
                          (!((exists j₆: int ::
                                  x₈ == j₆
                                  && 0 <= j₆
                                  && j₆ < 0)
                          )
                             ==> b[x₈] == b[x₈]))
                    && (forall j₆: int ::
                          (  j₆ <= j₆
                            && 0 <= j₆
                            && j₆ < 0
                             ==> j₆ < 100000))
                    && (forall a₂₄: [int]int, b₂₅: [int]int, j₂₆: int ::
                          (  true
                            && 0 <= j₂₆
                            && j₂₆ <= 100000
                            && (forall x₇: int ::
                                  ((exists j₆: int ::
                                          x₇ == j₆
                                          && 0 <= j₆
                                          && j₆ < j₂₆)
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, j₆: int ::
                                            j₆ < 100000
                                            && x₇ == j₆
                                            && 0 <= j₆
                                            && j₆ < j₂₆
                                            && a₂₄[x₇] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₇: int ::
                                  (!((exists j₆: int ::
                                          x₇ == j₆
                                          && 0 <= j₆
                                          && j₆ < j₂₆)
                                  )
                                     ==> a₂₄[x₇] == a[x₇]))
                            && (forall x₈: int ::
                                  ((exists j₆: int ::
                                          x₈ == j₆
                                          && 0 <= j₆
                                          && j₆ < j₂₆)
                                     ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                                            j₆ < 100000
                                            && x₈ == j₆
                                            && 0 <= j₆
                                            && j₆ < j₂₆
                                            && b₂₅[x₈] == __VERIFIER_nondet_int₂₅)))
                            && (forall x₈: int ::
                                  (!((exists j₆: int ::
                                          x₈ == j₆
                                          && 0 <= j₆
                                          && j₆ < j₂₆)
                                  )
                                     ==> b₂₅[x₈] == b[x₈]))
                            && (forall j₆: int ::
                                  (  j₆ <= j₆
                                    && 0 <= j₆
                                    && j₆ < j₂₆
                                     ==> j₆ < 100000))
                             ==> (j₂₆ < 100000
                                 ==> (forall __VERIFIER_nondet_int₁: int ::
                                      (forall __VERIFIER_nondet_int₂: int ::
                                              true
                                              && 0 <= j₂₆ + 1
                                              && j₂₆ + 1 <= 100000
                                              && (forall x₇: int ::
                                                    ((exists j₆: int ::
                                                            x₇ == j₆
                                                            && 0 <= j₆
                                                            && j₆ < j₂₆ + 1)
                                                       ==> (exists __VERIFIER_nondet_int₁₄: int, j₆: int ::
                                                              j₆ < 100000
                                                              && x₇ == j₆
                                                              && 0 <= j₆
                                                              && j₆ < j₂₆ + 1
                                                              && a₂₄[j₂₆ := __VERIFIER_nondet_int₁][x₇] == __VERIFIER_nondet_int₁₄)))
                                              && (forall x₇: int ::
                                                    (!((exists j₆: int ::
                                                            x₇ == j₆
                                                            && 0 <= j₆
                                                            && j₆ < j₂₆ + 1)
                                                    )
                                                       ==> a₂₄[j₂₆ := __VERIFIER_nondet_int₁][x₇] == a[x₇]))
                                              && (forall x₈: int ::
                                                    ((exists j₆: int ::
                                                            x₈ == j₆
                                                            && 0 <= j₆
                                                            && j₆ < j₂₆ + 1)
                                                       ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                                                              j₆ < 100000
                                                              && x₈ == j₆
                                                              && 0 <= j₆
                                                              && j₆ < j₂₆ + 1
                                                              && b₂₅[j₂₆ := __VERIFIER_nondet_int₂][x₈] == __VERIFIER_nondet_int₂₅)))
                                              && (forall x₈: int ::
                                                    (!((exists j₆: int ::
                                                            x₈ == j₆
                                                            && 0 <= j₆
                                                            && j₆ < j₂₆ + 1)
                                                    )
                                                       ==> b₂₅[j₂₆ := __VERIFIER_nondet_int₂][x₈] == b[x₈]))
                                              && (forall j₆: int ::
                                                    (  j₆ <= j₆
                                                      && 0 <= j₆
                                                      && j₆ < j₂₆ + 1
                                                       ==> j₆ < 100000))
                                              && true
                                              && (true
                                                 ==> true))))
                              && (!(j₂₆ < 100000
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= 100000
                                      && (forall x₁₄: int ::
                                            ((exists i₁₃: int ::
                                                    x₁₄ == i₁₃
                                                    && 0 <= i₁₃
                                                    && i₁₃ < 0)
                                               ==> (exists i₁₃: int ::
                                                        a₂₄[i₁₃] != b₂₅[i₁₃]
                                                        && i₁₃ < 100000
                                                        && x₁₄ == i₁₃
                                                        && 0 <= i₁₃
                                                        && i₁₃ < 0
                                                        && c[x₁₄] == a₂₄[i₁₃])
                                                || (exists i₁₃: int ::
                                                        a₂₄[i₁₃] == b₂₅[i₁₃]
                                                        && i₁₃ < 100000
                                                        && x₁₄ == i₁₃
                                                        && 0 <= i₁₃
                                                        && i₁₃ < 0
                                                        && c[x₁₄] == a₂₄[i₁₃])))
                                      && (forall x₁₄: int ::
                                            (!((exists i₁₃: int ::
                                                    x₁₄ == i₁₃
                                                    && 0 <= i₁₃
                                                    && i₁₃ < 0)
                                            )
                                               ==> c[x₁₄] == c[x₁₄]))
                                      && (forall i₁₃: int ::
                                            (  i₁₃ <= i₁₃
                                              && 0 <= i₁₃
                                              && i₁₃ < 0
                                               ==> i₁₃ < 100000))
                                      && (forall rv₂₇: int, c₂₈: [int]int, i₂₉: int ::
                                            (  true
                                              && 0 <= i₂₉
                                              && i₂₉ <= 100000
                                              && (forall x₁₄: int ::
                                                    ((exists i₁₃: int ::
                                                            x₁₄ == i₁₃
                                                            && 0 <= i₁₃
                                                            && i₁₃ < i₂₉)
                                                       ==> (exists i₁₃: int ::
                                                                a₂₄[i₁₃] != b₂₅[i₁₃]
                                                                && i₁₃ < 100000
                                                                && x₁₄ == i₁₃
                                                                && 0 <= i₁₃
                                                                && i₁₃ < i₂₉
                                                                && c₂₈[x₁₄] == a₂₄[i₁₃])
                                                        || (exists i₁₃: int ::
                                                                a₂₄[i₁₃] == b₂₅[i₁₃]
                                                                && i₁₃ < 100000
                                                                && x₁₄ == i₁₃
                                                                && 0 <= i₁₃
                                                                && i₁₃ < i₂₉
                                                                && c₂₈[x₁₄] == a₂₄[i₁₃])))
                                              && (forall x₁₄: int ::
                                                    (!((exists i₁₃: int ::
                                                            x₁₄ == i₁₃
                                                            && 0 <= i₁₃
                                                            && i₁₃ < i₂₉)
                                                    )
                                                       ==> c₂₈[x₁₄] == c[x₁₄]))
                                              && (forall i₁₃: int ::
                                                    (  i₁₃ <= i₁₃
                                                      && 0 <= i₁₃
                                                      && i₁₃ < i₂₉
                                                       ==> i₁₃ < 100000))
                                               ==> (i₂₉ < 100000
                                                   ==> (a₂₄[i₂₉] != b₂₅[i₂₉]
                                                       ==> true
                                                        && 0 <= i₂₉ + 1
                                                        && i₂₉ + 1 <= 100000
                                                        && (forall x₁₄: int ::
                                                              ((exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₂₉ + 1)
                                                                 ==> (exists i₁₃: int ::
                                                                          a₂₄[i₁₃] != b₂₅[i₁₃]
                                                                          && i₁₃ < 100000
                                                                          && x₁₄ == i₁₃
                                                                          && 0 <= i₁₃
                                                                          && i₁₃ < i₂₉ + 1
                                                                          && c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == a₂₄[i₁₃])
                                                                  || (exists i₁₃: int ::
                                                                          a₂₄[i₁₃] == b₂₅[i₁₃]
                                                                          && i₁₃ < 100000
                                                                          && x₁₄ == i₁₃
                                                                          && 0 <= i₁₃
                                                                          && i₁₃ < i₂₉ + 1
                                                                          && c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == a₂₄[i₁₃])))
                                                        && (forall x₁₄: int ::
                                                              (!((exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₂₉ + 1)
                                                              )
                                                                 ==> c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == c[x₁₄]))
                                                        && (forall i₁₃: int ::
                                                              (  i₁₃ <= i₁₃
                                                                && 0 <= i₁₃
                                                                && i₁₃ < i₂₉ + 1
                                                                 ==> i₁₃ < 100000))
                                                        && true
                                                        && (true
                                                           ==> true))
                                                    && (!(a₂₄[i₂₉] != b₂₅[i₂₉]
                                                    )
                                                       ==> true
                                                        && 0 <= i₂₉ + 1
                                                        && i₂₉ + 1 <= 100000
                                                        && (forall x₁₄: int ::
                                                              ((exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₂₉ + 1)
                                                                 ==> (exists i₁₃: int ::
                                                                          a₂₄[i₁₃] != b₂₅[i₁₃]
                                                                          && i₁₃ < 100000
                                                                          && x₁₄ == i₁₃
                                                                          && 0 <= i₁₃
                                                                          && i₁₃ < i₂₉ + 1
                                                                          && c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == a₂₄[i₁₃])
                                                                  || (exists i₁₃: int ::
                                                                          a₂₄[i₁₃] == b₂₅[i₁₃]
                                                                          && i₁₃ < 100000
                                                                          && x₁₄ == i₁₃
                                                                          && 0 <= i₁₃
                                                                          && i₁₃ < i₂₉ + 1
                                                                          && c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == a₂₄[i₁₃])))
                                                        && (forall x₁₄: int ::
                                                              (!((exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₂₉ + 1)
                                                              )
                                                                 ==> c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == c[x₁₄]))
                                                        && (forall i₁₃: int ::
                                                              (  i₁₃ <= i₁₃
                                                                && 0 <= i₁₃
                                                                && i₁₃ < i₂₉ + 1
                                                                 ==> i₁₃ < 100000))
                                                        && true
                                                        && (true
                                                           ==> true)))
                                                && (!(i₂₉ < 100000
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> (rv₂₇ != 0
                                                           ==> true
                                                            && 0 <= 0
                                                            && 0 <= 100000
                                                            && (forall x₁₉: int ::
                                                                  (  x₁₉ <= x₁₉
                                                                    && 0 <= x₁₉
                                                                    && x₁₉ < 0
                                                                     ==> x₁₉ < 100000))
                                                            && (forall x₃₀: int ::
                                                                  (  true
                                                                    && 0 <= x₃₀
                                                                    && x₃₀ <= 100000
                                                                    && (forall x₁₉: int ::
                                                                          (  x₁₉ <= x₁₉
                                                                            && 0 <= x₁₉
                                                                            && x₁₉ < x₃₀
                                                                             ==> x₁₉ < 100000))
                                                                     ==> (x₃₀ < 100000
                                                                         ==> a₂₄[x₃₀] == b₂₅[x₃₀]
                                                                          && (true
                                                                             ==> true
                                                                              && 0 <= x₃₀ + 1
                                                                              && x₃₀ + 1 <= 100000
                                                                              && (forall x₁₉: int ::
                                                                                    (  x₁₉ <= x₁₉
                                                                                      && 0 <= x₁₉
                                                                                      && x₁₉ < x₃₀ + 1
                                                                                       ==> x₁₉ < 100000))
                                                                              && true
                                                                              && (true
                                                                                 ==> true)))
                                                                      && (!(x₃₀ < 100000
                                                                      )
                                                                         ==> true
                                                                          && (true
                                                                             ==> true
                                                                              && 0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₂₁: int ::
                                                                                    (  x₂₁ <= x₂₁
                                                                                      && 0 <= x₂₁
                                                                                      && x₂₁ < 0
                                                                                       ==> x₂₁ < 100000))
                                                                              && (forall x₃₁: int ::
                                                                                    (  true
                                                                                      && 0 <= x₃₁
                                                                                      && x₃₁ <= 100000
                                                                                      && (forall x₂₁: int ::
                                                                                            (  x₂₁ <= x₂₁
                                                                                              && 0 <= x₂₁
                                                                                              && x₂₁ < x₃₁
                                                                                               ==> x₂₁ < 100000))
                                                                                       ==> (x₃₁ < 100000
                                                                                           ==> a₂₄[x₃₁] == c₂₈[x₃₁]
                                                                                            && (true
                                                                                               ==> true
                                                                                                && 0 <= x₃₁ + 1
                                                                                                && x₃₁ + 1 <= 100000
                                                                                                && (forall x₂₁: int ::
                                                                                                      (  x₂₁ <= x₂₁
                                                                                                        && 0 <= x₂₁
                                                                                                        && x₂₁ < x₃₁ + 1
                                                                                                         ==> x₂₁ < 100000))
                                                                                                && true
                                                                                                && (true
                                                                                                   ==> true)))
                                                                                        && (!(x₃₁ < 100000
                                                                                        )
                                                                                           ==> true
                                                                                            && (true
                                                                                               ==> true)))))))))
                                                        && (!(rv₂₇ != 0
                                                        )
                                                           ==> true
                                                            && 0 <= 0
                                                            && 0 <= 100000
                                                            && (forall x₂₁: int ::
                                                                  (  x₂₁ <= x₂₁
                                                                    && 0 <= x₂₁
                                                                    && x₂₁ < 0
                                                                     ==> x₂₁ < 100000))
                                                            && (forall x₃₄: int ::
                                                                  (  true
                                                                    && 0 <= x₃₄
                                                                    && x₃₄ <= 100000
                                                                    && (forall x₂₁: int ::
                                                                          (  x₂₁ <= x₂₁
                                                                            && 0 <= x₂₁
                                                                            && x₂₁ < x₃₄
                                                                             ==> x₂₁ < 100000))
                                                                     ==> (x₃₄ < 100000
                                                                         ==> a₂₄[x₃₄] == c₂₈[x₃₄]
                                                                          && (true
                                                                             ==> true
                                                                              && 0 <= x₃₄ + 1
                                                                              && x₃₄ + 1 <= 100000
                                                                              && (forall x₂₁: int ::
                                                                                    (  x₂₁ <= x₂₁
                                                                                      && 0 <= x₂₁
                                                                                      && x₂₁ < x₃₄ + 1
                                                                                       ==> x₂₁ < 100000))
                                                                              && true
                                                                              && (true
                                                                                 ==> true)))
                                                                      && (!(x₃₄ < 100000
                                                                      )
                                                                         ==> true
                                                                          && (true
                                                                             ==> true))))))))))))))));

