data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int ::
      (forall a: [int]int ::
            (0 < N₁₃
               ==> 0 <= 0
                && 0 <= 0
                && 0 <= N₁₃
                && (forall x₇: int, k₆: int ::
                      (  x₇ == k₆
                        && 0 <= k₆
                        && k₆ < 0
                         ==> (exists i₅: int, k₆: int ::
                                i₅ < N₁₃
                                && x₇ == k₆
                                && 0 <= k₆
                                && k₆ < 0
                                && a[x₇] == k₆)))
                && (forall x₇: int ::
                        (exists k₆: int ::
                                x₇ == k₆
                                && 0 <= k₆
                                && k₆ < 0)
                        || a[x₇] == a[x₇])
                && (forall i₅: int, k₆: int ::
                      (  0 <= i₅
                        && 0 <= k₆
                        && i₅ < 0
                        && k₆ < 0
                         ==> i₅ < N₁₃))
                && (forall a₁₄: [int]int, i₁₅: int, k₁₆: int ::
                      (  0 <= i₁₅
                        && 0 <= k₁₆
                        && i₁₅ <= N₁₃
                        && (forall x₇: int, k₆: int ::
                              (  x₇ == k₆
                                && 0 <= k₆
                                && k₆ < k₁₆
                                 ==> (exists i₅: int, k₆: int ::
                                        i₅ < N₁₃
                                        && x₇ == k₆
                                        && 0 <= k₆
                                        && k₆ < k₁₆
                                        && a₁₄[x₇] == k₆)))
                        && (forall x₇: int ::
                                (exists k₆: int ::
                                        x₇ == k₆
                                        && 0 <= k₆
                                        && k₆ < k₁₆)
                                || a₁₄[x₇] == a[x₇])
                        && (forall i₅: int, k₆: int ::
                              (  0 <= i₅
                                && 0 <= k₆
                                && i₅ < i₁₅
                                && k₆ < k₁₆
                                 ==> i₅ < N₁₃))
                         ==> (i₁₅ < N₁₃
                             ==> 0 <= i₁₅ + 1
                              && 0 <= k₁₆ + 1
                              && i₁₅ + 1 <= N₁₃
                              && (forall x₇: int, k₆: int ::
                                    (  x₇ == k₆
                                      && 0 <= k₆
                                      && k₆ < k₁₆ + 1
                                       ==> (exists i₅: int, k₆: int ::
                                              i₅ < N₁₃
                                              && x₇ == k₆
                                              && 0 <= k₆
                                              && k₆ < k₁₆ + 1
                                              && a₁₄[k₁₆ := k₁₆][x₇] == k₆)))
                              && (forall x₇: int ::
                                      (exists k₆: int ::
                                              x₇ == k₆
                                              && 0 <= k₆
                                              && k₆ < k₁₆ + 1)
                                      || a₁₄[k₁₆ := k₁₆][x₇] == a[x₇])
                              && (forall i₅: int, k₆: int ::
                                    (  0 <= i₅
                                      && 0 <= k₆
                                      && i₅ < i₁₅ + 1
                                      && k₆ < k₁₆ + 1
                                       ==> i₅ < N₁₃)))
                          &&   i₁₅ < N₁₃
                            ||   0 <= 0
                              && 0 <= N₁₃
                              && (forall i₁₁: int ::
                                    (  0 <= i₁₁
                                      && i₁₁ < 0
                                       ==> i₁₁ < N₁₃))
                              && (forall i₁₇: int ::
                                    (  0 <= i₁₇
                                      && i₁₇ <= N₁₃
                                      && (forall i₁₁: int ::
                                            (  0 <= i₁₁
                                              && i₁₁ < i₁₇
                                               ==> i₁₁ < N₁₃))
                                       ==> (i₁₇ < N₁₃
                                         ==> a₁₄[i₁₇] == i₁₇
                                          && 0 <= i₁₇ + 1
                                          && i₁₇ + 1 <= N₁₃
                                          && (forall i₁₁: int ::
                                                (  0 <= i₁₁
                                                  && i₁₁ < i₁₇ + 1
                                                   ==> i₁₁ < N₁₃))))))))));

