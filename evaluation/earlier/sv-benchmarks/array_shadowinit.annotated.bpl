data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₁₃: int ::
          (true
             ==> (0 < N₁₃
                 ==> (forall a: [int]int ::
                        true
                        && 0 <= 0
                        && 0 <= 0
                        && 0 <= N₁₃
                        && (forall x₇: int ::
                              ((exists k₆: int ::
                                      x₇ == k₆
                                      && 0 <= k₆
                                      && k₆ < 0)
                                 ==> (exists i₅: int, k₆: int ::
                                        i₅ < N₁₃
                                        && x₇ == k₆
                                        && 0 <= k₆
                                        && k₆ < 0
                                        && a[x₇] == k₆)))
                        && (forall x₇: int ::
                              (!((exists k₆: int ::
                                      x₇ == k₆
                                      && 0 <= k₆
                                      && k₆ < 0)
                              )
                                 ==> a[x₇] == a[x₇]))
                        && (forall i₅: int, k₆: int ::
                              (  i₅ <= i₅
                                && k₆ <= k₆
                                && 0 <= i₅
                                && i₅ < 0
                                && 0 <= k₆
                                && k₆ < 0
                                 ==> i₅ < N₁₃))
                        && (forall a₁₄: [int]int, i₁₅: int, k₁₆: int ::
                              (  true
                                && 0 <= i₁₅
                                && 0 <= k₁₆
                                && i₁₅ <= N₁₃
                                && (forall x₇: int ::
                                      ((exists k₆: int ::
                                              x₇ == k₆
                                              && 0 <= k₆
                                              && k₆ < k₁₆)
                                         ==> (exists i₅: int, k₆: int ::
                                                i₅ < N₁₃
                                                && x₇ == k₆
                                                && 0 <= k₆
                                                && k₆ < k₁₆
                                                && a₁₄[x₇] == k₆)))
                                && (forall x₇: int ::
                                      (!((exists k₆: int ::
                                              x₇ == k₆
                                              && 0 <= k₆
                                              && k₆ < k₁₆)
                                      )
                                         ==> a₁₄[x₇] == a[x₇]))
                                && (forall i₅: int, k₆: int ::
                                      (  i₅ <= i₅
                                        && k₆ <= k₆
                                        && 0 <= i₅
                                        && i₅ < i₁₅
                                        && 0 <= k₆
                                        && k₆ < k₁₆
                                         ==> i₅ < N₁₃))
                                 ==> (i₁₅ < N₁₃
                                     ==> true
                                      && 0 <= i₁₅ + 1
                                      && 0 <= k₁₆ + 1
                                      && i₁₅ + 1 <= N₁₃
                                      && (forall x₇: int ::
                                            ((exists k₆: int ::
                                                    x₇ == k₆
                                                    && 0 <= k₆
                                                    && k₆ < k₁₆ + 1)
                                               ==> (exists i₅: int, k₆: int ::
                                                      i₅ < N₁₃
                                                      && x₇ == k₆
                                                      && 0 <= k₆
                                                      && k₆ < k₁₆ + 1
                                                      && a₁₄[k₁₆ := k₁₆][x₇] == k₆)))
                                      && (forall x₇: int ::
                                            (!((exists k₆: int ::
                                                    x₇ == k₆
                                                    && 0 <= k₆
                                                    && k₆ < k₁₆ + 1)
                                            )
                                               ==> a₁₄[k₁₆ := k₁₆][x₇] == a[x₇]))
                                      && (forall i₅: int, k₆: int ::
                                            (  i₅ <= i₅
                                              && k₆ <= k₆
                                              && 0 <= i₅
                                              && i₅ < i₁₅ + 1
                                              && 0 <= k₆
                                              && k₆ < k₁₆ + 1
                                               ==> i₅ < N₁₃))
                                      && true
                                      && (true
                                         ==> true))
                                  && (!(i₁₅ < N₁₃
                                  )
                                     ==> true
                                      && (true
                                         ==> true
                                          && 0 <= 0
                                          && 0 <= N₁₃
                                          && (forall i₁₁: int ::
                                                (  i₁₁ <= i₁₁
                                                  && 0 <= i₁₁
                                                  && i₁₁ < 0
                                                   ==> i₁₁ < N₁₃))
                                          && (forall i₁₇: int ::
                                                (  true
                                                  && 0 <= i₁₇
                                                  && i₁₇ <= N₁₃
                                                  && (forall i₁₁: int ::
                                                        (  i₁₁ <= i₁₁
                                                          && 0 <= i₁₁
                                                          && i₁₁ < i₁₇
                                                           ==> i₁₁ < N₁₃))
                                                   ==> (i₁₇ < N₁₃
                                                       ==> a₁₄[i₁₇] == i₁₇
                                                        && (true
                                                           ==> true
                                                            && 0 <= i₁₇ + 1
                                                            && i₁₇ + 1 <= N₁₃
                                                            && (forall i₁₁: int ::
                                                                  (  i₁₁ <= i₁₁
                                                                    && 0 <= i₁₁
                                                                    && i₁₁ < i₁₇ + 1
                                                                     ==> i₁₁ < N₁₃))
                                                            && true
                                                            && (true
                                                               ==> true)))
                                                    && (!(i₁₇ < N₁₃
                                                    )
                                                       ==> true
                                                        && (true
                                                           ==> true))))))))))
              && (!(0 < N₁₃
              )
                 ==> true))));

