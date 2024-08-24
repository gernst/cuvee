data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall CELLCOUNT₁₄: int ::
      (forall volArray: [int]int ::
            (1 < CELLCOUNT₁₄
               ==> (CELLCOUNT₁₄ % 2 == 0
                 ==> (CELLCOUNT₁₄ % 2 == 0
                   ==> 1 <= 1
                    && 1 <= 1 + CELLCOUNT₁₄ / 2
                    && (forall x₅: int, i₄: int ::
                          (  (x₅ == -1 + 2 * i₄
                               ==> 1 <= i₄
                                && i₄ < 1)
                            &&   x₅ == -1 + 2 * i₄
                              ||   x₅ == -2 + 2 * i₄
                                && 1 <= i₄
                                && i₄ < 1
                             ==> (exists i₄: int ::
                                      2 <= 3
                                      && i₄ <= CELLCOUNT₁₄ / 2
                                      && if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < 1 && volArray[x₅] == volArray[-2 + 2 * i₄ := 3][-1 + 2 * i₄] else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < 1 && volArray[x₅] == 3)
                              || (2 <= 3
                                 ==> false)))
                    && (forall x₅: int ::
                            (exists i₄: int ::
                                  if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < 1 else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < 1)
                            || volArray[x₅] == volArray[x₅])
                    && (forall i₄: int ::
                          (  1 <= i₄
                            && i₄ < 1
                             ==> i₄ <= CELLCOUNT₁₄ / 2))
                    && (forall volArray₁₅: [int]int, i₁₆: int ::
                          (  1 <= i₁₆
                            && i₁₆ <= 1 + CELLCOUNT₁₄ / 2
                            && (forall x₅: int, i₄: int ::
                                  (  (x₅ == -1 + 2 * i₄
                                       ==> 1 <= i₄
                                        && i₄ < i₁₆)
                                    &&   x₅ == -1 + 2 * i₄
                                      ||   x₅ == -2 + 2 * i₄
                                        && 1 <= i₄
                                        && i₄ < i₁₆
                                     ==> (exists i₄: int ::
                                              2 <= 3
                                              && i₄ <= CELLCOUNT₁₄ / 2
                                              && if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ && volArray₁₅[x₅] == volArray₁₅[-2 + 2 * i₄ := 3][-1 + 2 * i₄] else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆ && volArray₁₅[x₅] == 3)
                                      || (2 <= 3
                                         ==> false)))
                            && (forall x₅: int ::
                                    (exists i₄: int ::
                                          if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆)
                                    || volArray₁₅[x₅] == volArray[x₅])
                            && (forall i₄: int ::
                                  (  1 <= i₄
                                    && i₄ < i₁₆
                                     ==> i₄ <= CELLCOUNT₁₄ / 2))
                             ==> (i₁₆ <= CELLCOUNT₁₄ / 2
                                 ==> (2 <= 3
                                     ==> 1 <= i₁₆ + 1
                                      && i₁₆ + 1 <= 1 + CELLCOUNT₁₄ / 2
                                      && (forall x₅: int, i₄: int ::
                                            (  (x₅ == -1 + 2 * i₄
                                                 ==> 1 <= i₄
                                                  && i₄ < i₁₆ + 1)
                                              &&   x₅ == -1 + 2 * i₄
                                                ||   x₅ == -2 + 2 * i₄
                                                  && 1 <= i₄
                                                  && i₄ < i₁₆ + 1
                                               ==> (exists i₄: int ::
                                                        2 <= 3
                                                        && i₄ <= CELLCOUNT₁₄ / 2
                                                        && if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ + 1 && volArray₁₅[i₁₆ * 2 - 2 := 3][i₁₆ * 2 - 1 := volArray₁₅[i₁₆ * 2 - 2 := 3][i₁₆ * 2 - 1]][x₅] == volArray₁₅[i₁₆ * 2 - 2 := 3][i₁₆ * 2 - 1 := volArray₁₅[i₁₆ * 2 - 2 := 3][i₁₆ * 2 - 1]][-2 + 2 * i₄ := 3][-1 + 2 * i₄] else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆ + 1 && volArray₁₅[i₁₆ * 2 - 2 := 3][i₁₆ * 2 - 1 := volArray₁₅[i₁₆ * 2 - 2 := 3][i₁₆ * 2 - 1]][x₅] == 3)
                                                || (2 <= 3
                                                   ==> false)))
                                      && (forall x₅: int ::
                                              (exists i₄: int ::
                                                    if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ + 1 else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆ + 1)
                                              || volArray₁₅[i₁₆ * 2 - 2 := 3][i₁₆ * 2 - 1 := volArray₁₅[i₁₆ * 2 - 2 := 3][i₁₆ * 2 - 1]][x₅] == volArray[x₅])
                                      && (forall i₄: int ::
                                            (  1 <= i₄
                                              && i₄ < i₁₆ + 1
                                               ==> i₄ <= CELLCOUNT₁₄ / 2)))
                                  &&   2 <= 3
                                    ||   1 <= i₁₆ + 1
                                      && i₁₆ + 1 <= 1 + CELLCOUNT₁₄ / 2
                                      && (forall x₅: int, i₄: int ::
                                            (  (x₅ == -1 + 2 * i₄
                                                 ==> 1 <= i₄
                                                  && i₄ < i₁₆ + 1)
                                              &&   x₅ == -1 + 2 * i₄
                                                ||   x₅ == -2 + 2 * i₄
                                                  && 1 <= i₄
                                                  && i₄ < i₁₆ + 1
                                               ==> (exists i₄: int ::
                                                        2 <= 3
                                                        && i₄ <= CELLCOUNT₁₄ / 2
                                                        && if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ + 1 && volArray₁₅[i₁₆ * 2 - 2 := 0][i₁₆ * 2 - 1 := volArray₁₅[i₁₆ * 2 - 2 := 0][i₁₆ * 2 - 1]][x₅] == volArray₁₅[i₁₆ * 2 - 2 := 0][i₁₆ * 2 - 1 := volArray₁₅[i₁₆ * 2 - 2 := 0][i₁₆ * 2 - 1]][-2 + 2 * i₄ := 3][-1 + 2 * i₄] else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆ + 1 && volArray₁₅[i₁₆ * 2 - 2 := 0][i₁₆ * 2 - 1 := volArray₁₅[i₁₆ * 2 - 2 := 0][i₁₆ * 2 - 1]][x₅] == 3)
                                                || (2 <= 3
                                                   ==> false)))
                                      && (forall x₅: int ::
                                              (exists i₄: int ::
                                                    if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ + 1 else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆ + 1)
                                              || volArray₁₅[i₁₆ * 2 - 2 := 0][i₁₆ * 2 - 1 := volArray₁₅[i₁₆ * 2 - 2 := 0][i₁₆ * 2 - 1]][x₅] == volArray[x₅])
                                      && (forall i₄: int ::
                                            (  1 <= i₄
                                              && i₄ < i₁₆ + 1
                                               ==> i₄ <= CELLCOUNT₁₄ / 2)))
                              &&   i₁₆ <= CELLCOUNT₁₄ / 2
                                ||   1 <= 1
                                  && 1 <= 1 + CELLCOUNT₁₄ / 2
                                  && (forall x₉: int, i₈: int ::
                                        (  (x₉ == -2 + 2 * i₈
                                             ==> 1 <= i₈
                                              && i₈ < 1)
                                          &&   x₉ == -2 + 2 * i₈
                                            ||   x₉ == -1 + 2 * i₈
                                              && 1 <= i₈
                                              && i₈ < 1
                                           ==> (exists i₈: int ::
                                                    2 <= 1
                                                    && i₈ <= CELLCOUNT₁₄ / 2
                                                    && if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < 1 && volArray₁₅[x₉] == volArray₁₅[-1 + 2 * i₈ := 1][-2 + 2 * i₈] else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < 1 && volArray₁₅[x₉] == 1)
                                            || (2 <= 1
                                               ==> false)))
                                  && (forall x₉: int ::
                                          (exists i₈: int ::
                                                if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < 1 else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < 1)
                                          || volArray₁₅[x₉] == volArray₁₅[x₉])
                                  && (forall i₈: int ::
                                        (  1 <= i₈
                                          && i₈ < 1
                                           ==> i₈ <= CELLCOUNT₁₄ / 2))
                                  && (forall volArray₁₇: [int]int, i₁₈: int ::
                                        (  1 <= i₁₈
                                          && i₁₈ <= 1 + CELLCOUNT₁₄ / 2
                                          && (forall x₉: int, i₈: int ::
                                                (  (x₉ == -2 + 2 * i₈
                                                     ==> 1 <= i₈
                                                      && i₈ < i₁₈)
                                                  &&   x₉ == -2 + 2 * i₈
                                                    ||   x₉ == -1 + 2 * i₈
                                                      && 1 <= i₈
                                                      && i₈ < i₁₈
                                                   ==> (exists i₈: int ::
                                                            2 <= 1
                                                            && i₈ <= CELLCOUNT₁₄ / 2
                                                            && if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ && volArray₁₇[x₉] == volArray₁₇[-1 + 2 * i₈ := 1][-2 + 2 * i₈] else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈ && volArray₁₇[x₉] == 1)
                                                    || (2 <= 1
                                                       ==> false)))
                                          && (forall x₉: int ::
                                                  (exists i₈: int ::
                                                        if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈)
                                                  || volArray₁₇[x₉] == volArray₁₅[x₉])
                                          && (forall i₈: int ::
                                                (  1 <= i₈
                                                  && i₈ < i₁₈
                                                   ==> i₈ <= CELLCOUNT₁₄ / 2))
                                           ==> (i₁₈ <= CELLCOUNT₁₄ / 2
                                               ==> (2 <= 1
                                                   ==> 1 <= i₁₈ + 1
                                                    && i₁₈ + 1 <= 1 + CELLCOUNT₁₄ / 2
                                                    && (forall x₉: int, i₈: int ::
                                                          (  (x₉ == -2 + 2 * i₈
                                                               ==> 1 <= i₈
                                                                && i₈ < i₁₈ + 1)
                                                            &&   x₉ == -2 + 2 * i₈
                                                              ||   x₉ == -1 + 2 * i₈
                                                                && 1 <= i₈
                                                                && i₈ < i₁₈ + 1
                                                             ==> (exists i₈: int ::
                                                                      2 <= 1
                                                                      && i₈ <= CELLCOUNT₁₄ / 2
                                                                      && if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ + 1 && volArray₁₇[i₁₈ * 2 - 1 := 1][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 1][i₁₈ * 2 - 2]][x₉] == volArray₁₇[i₁₈ * 2 - 1 := 1][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 1][i₁₈ * 2 - 2]][-1 + 2 * i₈ := 1][-2 + 2 * i₈] else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈ + 1 && volArray₁₇[i₁₈ * 2 - 1 := 1][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 1][i₁₈ * 2 - 2]][x₉] == 1)
                                                              || (2 <= 1
                                                                 ==> false)))
                                                    && (forall x₉: int ::
                                                            (exists i₈: int ::
                                                                  if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ + 1 else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈ + 1)
                                                            || volArray₁₇[i₁₈ * 2 - 1 := 1][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 1][i₁₈ * 2 - 2]][x₉] == volArray₁₅[x₉])
                                                    && (forall i₈: int ::
                                                          (  1 <= i₈
                                                            && i₈ < i₁₈ + 1
                                                             ==> i₈ <= CELLCOUNT₁₄ / 2)))
                                                &&   2 <= 1
                                                  ||   1 <= i₁₈ + 1
                                                    && i₁₈ + 1 <= 1 + CELLCOUNT₁₄ / 2
                                                    && (forall x₉: int, i₈: int ::
                                                          (  (x₉ == -2 + 2 * i₈
                                                               ==> 1 <= i₈
                                                                && i₈ < i₁₈ + 1)
                                                            &&   x₉ == -2 + 2 * i₈
                                                              ||   x₉ == -1 + 2 * i₈
                                                                && 1 <= i₈
                                                                && i₈ < i₁₈ + 1
                                                             ==> (exists i₈: int ::
                                                                      2 <= 1
                                                                      && i₈ <= CELLCOUNT₁₄ / 2
                                                                      && if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ + 1 && volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2]][x₉] == volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2]][-1 + 2 * i₈ := 1][-2 + 2 * i₈] else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈ + 1 && volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2]][x₉] == 1)
                                                              || (2 <= 1
                                                                 ==> false)))
                                                    && (forall x₉: int ::
                                                            (exists i₈: int ::
                                                                  if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ + 1 else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈ + 1)
                                                            || volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2]][x₉] == volArray₁₅[x₉])
                                                    && (forall i₈: int ::
                                                          (  1 <= i₈
                                                            && i₈ < i₁₈ + 1
                                                             ==> i₈ <= CELLCOUNT₁₄ / 2)))
                                            &&   i₁₈ <= CELLCOUNT₁₄ / 2
                                              ||   0 <= 0
                                                && 0 <= CELLCOUNT₁₄
                                                && (forall i₁₂: int ::
                                                      (  0 <= i₁₂
                                                        && i₁₂ < 0
                                                         ==> i₁₂ < CELLCOUNT₁₄))
                                                && (forall i₁₉: int ::
                                                      (  0 <= i₁₉
                                                        && i₁₉ <= CELLCOUNT₁₄
                                                        && (forall i₁₂: int ::
                                                              (  0 <= i₁₂
                                                                && i₁₂ < i₁₉
                                                                 ==> i₁₂ < CELLCOUNT₁₄))
                                                         ==> (i₁₉ < CELLCOUNT₁₄
                                                           ==> 2 <= volArray₁₇[i₁₉]
                                                              || volArray₁₇[i₁₉] == 0
                                                            && 0 <= i₁₉ + 1
                                                            && i₁₉ + 1 <= CELLCOUNT₁₄
                                                            && (forall i₁₂: int ::
                                                                  (  0 <= i₁₂
                                                                    && i₁₂ < i₁₉ + 1
                                                                     ==> i₁₂ < CELLCOUNT₁₄))))))))))))));

