data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> (forall N: int ::
        (forall a: [int]int ::
                true
                && (0 < N
                   ==> true
                    && 1 <= 1
                    && 1 <= N
                    && (forall x₉: int ::
                          ((exists i₈: int ::
                                  x₉ == i₈
                                  && 1 <= i₈
                                  && i₈ < 1)
                             ==> (exists j₇: int, i₈: int ::
                                    0 <= j₇
                                    && j₇ < 10000
                                    && i₈ < N
                                    && x₉ == i₈
                                    && 1 <= i₈
                                    && i₈ < 1
                                    && a[x₉] == j₇)))
                    && (forall x₉: int ::
                          (!((exists i₈: int ::
                                  x₉ == i₈
                                  && 1 <= i₈
                                  && i₈ < 1)
                          )
                             ==> a[x₉] == a[x₉]))
                    && (forall i₈: int ::
                          (  1 <= i₈
                            && i₈ < 1
                             ==> i₈ < N))
                    && (forall a₁₈: [int]int, i₁₉: int ::
                          (  true
                            && 1 <= i₁₉
                            && i₁₉ <= N
                            && (forall x₉: int ::
                                  ((exists i₈: int ::
                                          x₉ == i₈
                                          && 1 <= i₈
                                          && i₈ < i₁₉)
                                     ==> (exists j₇: int, i₈: int ::
                                            0 <= j₇
                                            && j₇ < 10000
                                            && i₈ < N
                                            && x₉ == i₈
                                            && 1 <= i₈
                                            && i₈ < i₁₉
                                            && a₁₈[x₉] == j₇)))
                            && (forall x₉: int ::
                                  (!((exists i₈: int ::
                                          x₉ == i₈
                                          && 1 <= i₈
                                          && i₈ < i₁₉)
                                  )
                                     ==> a₁₈[x₉] == a[x₉]))
                            && (forall i₈: int ::
                                  (  1 <= i₈
                                    && i₈ < i₁₉
                                     ==> i₈ < N))
                             ==> (i₁₉ < N
                                 ==> (forall j: int ::
                                        true
                                        && (  0 <= j
                                          && j < 10000
                                           ==> true
                                            && 1 <= i₁₉ + 1
                                            && i₁₉ + 1 <= N
                                            && (forall x₉: int ::
                                                  ((exists i₈: int ::
                                                          x₉ == i₈
                                                          && 1 <= i₈
                                                          && i₈ < i₁₉ + 1)
                                                     ==> (exists j₇: int, i₈: int ::
                                                            0 <= j₇
                                                            && j₇ < 10000
                                                            && i₈ < N
                                                            && x₉ == i₈
                                                            && 1 <= i₈
                                                            && i₈ < i₁₉ + 1
                                                            && a₁₈[i₁₉ := j][x₉] == j₇)))
                                            && (forall x₉: int ::
                                                  (!((exists i₈: int ::
                                                          x₉ == i₈
                                                          && 1 <= i₈
                                                          && i₈ < i₁₉ + 1)
                                                  )
                                                     ==> a₁₈[i₁₉ := j][x₉] == a[x₉]))
                                            && (forall i₈: int ::
                                                  (  1 <= i₈
                                                    && i₈ < i₁₉ + 1
                                                     ==> i₈ < N))
                                            && true
                                            && (true
                                               ==> true))))
                              && (!(i₁₉ < N
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= N
                                      && (forall x₁₃: int ::
                                            ((exists i₁₂: int ::
                                                  if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < 0 else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < 0)
                                               ==> (exists i₁₂: int ::
                                                      i₁₂ < N
                                                      && if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < 0 && a₁₈[x₁₃] == 2 + a₁₈[i₁₂] else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < 0 && a₁₈[x₁₃] == 1 + a₁₈[i₁₂])))
                                      && (forall x₁₃: int ::
                                            (!((exists i₁₂: int ::
                                                  if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < 0 else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < 0)
                                            )
                                               ==> a₁₈[x₁₃] == a₁₈[x₁₃]))
                                      && (forall i₁₂: int ::
                                            (  0 <= i₁₂
                                              && i₁₂ < 0
                                               ==> i₁₂ < N))
                                      && (forall a₂₀: [int]int, i₂₁: int ::
                                            (  true
                                              && 0 <= i₂₁
                                              && i₂₁ <= N
                                              && (forall x₁₃: int ::
                                                    ((exists i₁₂: int ::
                                                          if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < i₂₁ else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < i₂₁)
                                                       ==> (exists i₁₂: int ::
                                                              i₁₂ < N
                                                              && if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < i₂₁ && a₂₀[x₁₃] == 2 + a₁₈[i₁₂] else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < i₂₁ && a₂₀[x₁₃] == 1 + a₁₈[i₁₂])))
                                              && (forall x₁₃: int ::
                                                    (!((exists i₁₂: int ::
                                                          if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < i₂₁ else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < i₂₁)
                                                    )
                                                       ==> a₂₀[x₁₃] == a₁₈[x₁₃]))
                                              && (forall i₁₂: int ::
                                                    (  0 <= i₁₂
                                                      && i₁₂ < i₂₁
                                                       ==> i₁₂ < N))
                                               ==> (i₂₁ < N
                                                   ==> true
                                                    && 0 <= i₂₁ + 1
                                                    && i₂₁ + 1 <= N
                                                    && (forall x₁₃: int ::
                                                          ((exists i₁₂: int ::
                                                                if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < i₂₁ + 1 else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < i₂₁ + 1)
                                                             ==> (exists i₁₂: int ::
                                                                    i₁₂ < N
                                                                    && if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < i₂₁ + 1 && a₂₀[i₂₁ := a₂₀[i₂₁] + 1][i₂₁ := a₂₀[i₂₁ := a₂₀[i₂₁] + 1][i₂₁] + 1][x₁₃] == 2 + a₁₈[i₁₂] else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < i₂₁ + 1 && a₂₀[i₂₁ := a₂₀[i₂₁] + 1][i₂₁ := a₂₀[i₂₁ := a₂₀[i₂₁] + 1][i₂₁] + 1][x₁₃] == 1 + a₁₈[i₁₂])))
                                                    && (forall x₁₃: int ::
                                                          (!((exists i₁₂: int ::
                                                                if(x₁₃ == i₁₂) then 0 <= i₁₂ && i₁₂ < i₂₁ + 1 else x₁₃ == i₁₂ && 0 <= i₁₂ && i₁₂ < i₂₁ + 1)
                                                          )
                                                             ==> a₂₀[i₂₁ := a₂₀[i₂₁] + 1][i₂₁ := a₂₀[i₂₁ := a₂₀[i₂₁] + 1][i₂₁] + 1][x₁₃] == a₁₈[x₁₃]))
                                                    && (forall i₁₂: int ::
                                                          (  0 <= i₁₂
                                                            && i₁₂ < i₂₁ + 1
                                                             ==> i₁₂ < N))
                                                    && true
                                                    && (true
                                                       ==> true))
                                                && (!(i₂₁ < N
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 1 <= 1
                                                        && 1 <= N
                                                        && (forall i₁₆: int ::
                                                              (  1 <= i₁₆
                                                                && i₁₆ < 1
                                                                 ==> i₁₆ < N))
                                                        && (forall i₂₂: int ::
                                                              (  true
                                                                && 1 <= i₂₂
                                                                && i₂₂ <= N
                                                                && (forall i₁₆: int ::
                                                                      (  1 <= i₁₆
                                                                        && i₁₆ < i₂₂
                                                                         ==> i₁₆ < N))
                                                                 ==> (i₂₂ < N
                                                                     ==> 2 <= a₂₀[i₂₂]
                                                                      && (true
                                                                         ==> true
                                                                          && 1 <= i₂₂ + 1
                                                                          && i₂₂ + 1 <= N
                                                                          && (forall i₁₆: int ::
                                                                                (  1 <= i₁₆
                                                                                  && i₁₆ < i₂₂ + 1
                                                                                   ==> i₁₆ < N))
                                                                          && true
                                                                          && (true
                                                                             ==> true)))
                                                                  && (!(i₂₂ < N
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true))))))))))))))));

