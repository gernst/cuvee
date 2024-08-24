data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall CELLCOUNT₁₁: int ::
      (forall MINVAL: int, volArray: [int]int ::
            (1 < CELLCOUNT₁₁
               ==> (CELLCOUNT₁₁ % 5 == 0
                 ==> (CELLCOUNT₁₁ % 5 == 0
                   ==> 1 <= 1
                    && 1 <= 1 + CELLCOUNT₁₁ / 5
                    && (forall x₆: int, i₅: int ::
                          (  (x₆ == -1 + 5 * i₅
                               ==> 1 <= i₅
                                && i₅ < 1)
                            &&   x₆ == -1 + 5 * i₅
                              ||   x₆ == -2 + 5 * i₅
                                && 1 <= i₅
                                && i₅ < 1
                              || (x₆ == -2 + 5 * i₅
                                 ==> false)
                             ==> (exists i₅: int ::
                                      MINVAL <= 1
                                      && MINVAL <= 3
                                      && MINVAL <= 7
                                      && MINVAL <= 5
                                      && MINVAL <= 2
                                      && i₅ <= CELLCOUNT₁₁ / 5
                                      && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 2)
                              ||   MINVAL <= 1
                                && MINVAL <= 3
                                && MINVAL <= 7
                                && MINVAL <= 5
                                && (MINVAL <= 2
                                   ==> false)
                              ||   MINVAL <= 1
                                && MINVAL <= 3
                                && MINVAL <= 7
                                && (MINVAL <= 5
                                   ==> false)
                              ||   MINVAL <= 1
                                && MINVAL <= 3
                                && MINVAL <= 7
                                && (MINVAL <= 5
                                   ==> false)
                              ||   MINVAL <= 1
                                && MINVAL <= 3
                                && (MINVAL <= 7
                                   ==> false)
                              ||   MINVAL <= 1
                                && MINVAL <= 3
                                && (MINVAL <= 7
                                   ==> false)
                              ||   MINVAL <= 1
                                && MINVAL <= 3
                                && (MINVAL <= 7
                                   ==> false)
                              ||   MINVAL <= 1
                                && MINVAL <= 3
                                && (MINVAL <= 7
                                   ==> false)
                              ||   MINVAL <= 1
                                && (MINVAL <= 3
                                   ==> false)
                              ||   MINVAL <= 1
                                && (MINVAL <= 3
                                   ==> false)
                              ||   MINVAL <= 1
                                && (MINVAL <= 3
                                   ==> false)
                              ||   MINVAL <= 1
                                && (MINVAL <= 3
                                   ==> false)
                              ||   MINVAL <= 1
                                && (MINVAL <= 3
                                   ==> false)
                              ||   MINVAL <= 1
                                && (MINVAL <= 3
                                   ==> false)
                              ||   MINVAL <= 1
                                && (MINVAL <= 3
                                   ==> false)
                              ||   MINVAL <= 1
                                && (MINVAL <= 3
                                   ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)
                              || (MINVAL <= 1
                                 ==> false)))
                    && (forall x₆: int ::
                            (exists i₅: int ::
                                  if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < 1)
                            || volArray[x₆] == volArray[x₆])
                    && (forall i₅: int ::
                          (  1 <= i₅
                            && i₅ < 1
                             ==> i₅ <= CELLCOUNT₁₁ / 5))
                    && (forall volArray₁₂: [int]int, i₁₃: int ::
                          (  1 <= i₁₃
                            && i₁₃ <= 1 + CELLCOUNT₁₁ / 5
                            && (forall x₆: int, i₅: int ::
                                  (  (x₆ == -1 + 5 * i₅
                                       ==> 1 <= i₅
                                        && i₅ < i₁₃)
                                    &&   x₆ == -1 + 5 * i₅
                                      ||   x₆ == -2 + 5 * i₅
                                        && 1 <= i₅
                                        && i₅ < i₁₃
                                      || (x₆ == -2 + 5 * i₅
                                         ==> false)
                                     ==> (exists i₅: int ::
                                              MINVAL <= 1
                                              && MINVAL <= 3
                                              && MINVAL <= 7
                                              && MINVAL <= 5
                                              && MINVAL <= 2
                                              && i₅ <= CELLCOUNT₁₁ / 5
                                              && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 2)
                                      ||   MINVAL <= 1
                                        && MINVAL <= 3
                                        && MINVAL <= 7
                                        && MINVAL <= 5
                                        && (MINVAL <= 2
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && MINVAL <= 3
                                        && MINVAL <= 7
                                        && (MINVAL <= 5
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && MINVAL <= 3
                                        && MINVAL <= 7
                                        && (MINVAL <= 5
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && MINVAL <= 3
                                        && (MINVAL <= 7
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && MINVAL <= 3
                                        && (MINVAL <= 7
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && MINVAL <= 3
                                        && (MINVAL <= 7
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && MINVAL <= 3
                                        && (MINVAL <= 7
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && (MINVAL <= 3
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && (MINVAL <= 3
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && (MINVAL <= 3
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && (MINVAL <= 3
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && (MINVAL <= 3
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && (MINVAL <= 3
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && (MINVAL <= 3
                                           ==> false)
                                      ||   MINVAL <= 1
                                        && (MINVAL <= 3
                                           ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)
                                      || (MINVAL <= 1
                                         ==> false)))
                            && (forall x₆: int ::
                                    (exists i₅: int ::
                                          if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃)
                                    || volArray₁₂[x₆] == volArray[x₆])
                            && (forall i₅: int ::
                                  (  1 <= i₅
                                    && i₅ < i₁₃
                                     ==> i₅ <= CELLCOUNT₁₁ / 5))
                             ==> (i₁₃ <= CELLCOUNT₁₁ / 5
                                 ==> (MINVAL <= 2
                                     ==> (MINVAL <= 5
                                         ==> (MINVAL <= 7
                                             ==> (MINVAL <= 3
                                                 ==> (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                              &&   MINVAL <= 3
                                                ||   (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                          &&   MINVAL <= 7
                                            ||   (MINVAL <= 3
                                                 ==> (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                              &&   MINVAL <= 3
                                                ||   (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                      &&   MINVAL <= 5
                                        ||   (MINVAL <= 7
                                             ==> (MINVAL <= 3
                                                 ==> (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                              &&   MINVAL <= 3
                                                ||   (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                          &&   MINVAL <= 7
                                            ||   (MINVAL <= 3
                                                 ==> (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                              &&   MINVAL <= 3
                                                ||   (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 2][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                  &&   MINVAL <= 2
                                    ||   (MINVAL <= 5
                                         ==> (MINVAL <= 7
                                             ==> (MINVAL <= 3
                                                 ==> (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                              &&   MINVAL <= 3
                                                ||   (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                          &&   MINVAL <= 7
                                            ||   (MINVAL <= 3
                                                 ==> (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                              &&   MINVAL <= 3
                                                ||   (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 5][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                      &&   MINVAL <= 5
                                        ||   (MINVAL <= 7
                                             ==> (MINVAL <= 3
                                                 ==> (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                              &&   MINVAL <= 3
                                                ||   (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 7][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                          &&   MINVAL <= 7
                                            ||   (MINVAL <= 3
                                                 ==> (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 3][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                              &&   MINVAL <= 3
                                                ||   (MINVAL <= 1
                                                     ==> 1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 1][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                                                  &&   MINVAL <= 1
                                                    ||   1 <= i₁₃ + 1
                                                      && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 5
                                                      && (forall x₆: int, i₅: int ::
                                                            (  (x₆ == -1 + 5 * i₅
                                                                 ==> 1 <= i₅
                                                                  && i₅ < i₁₃ + 1)
                                                              &&   x₆ == -1 + 5 * i₅
                                                                ||   x₆ == -2 + 5 * i₅
                                                                  && 1 <= i₅
                                                                  && i₅ < i₁₃ + 1
                                                                || (x₆ == -2 + 5 * i₅
                                                                   ==> false)
                                                               ==> (exists i₅: int ::
                                                                        MINVAL <= 1
                                                                        && MINVAL <= 3
                                                                        && MINVAL <= 7
                                                                        && MINVAL <= 5
                                                                        && MINVAL <= 2
                                                                        && i₅ <= CELLCOUNT₁₁ / 5
                                                                        && if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 3 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 7 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 5 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == 2)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && MINVAL <= 5
                                                                  && (MINVAL <= 2
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && MINVAL <= 7
                                                                  && (MINVAL <= 5
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && MINVAL <= 3
                                                                  && (MINVAL <= 7
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                ||   MINVAL <= 1
                                                                  && (MINVAL <= 3
                                                                     ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)
                                                                || (MINVAL <= 1
                                                                   ==> false)))
                                                      && (forall x₆: int ::
                                                              (exists i₅: int ::
                                                                    if(x₆ == -1 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -3 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -4 + 5 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -5 + 5 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                              || volArray₁₂[i₁₃ * 5 - 5 := 0][i₁₃ * 5 - 4 := 0][i₁₃ * 5 - 3 := 0][i₁₃ * 5 - 2 := 0][i₁₃ * 5 - 1 := 0][x₆] == volArray[x₆])
                                                      && (forall i₅: int ::
                                                            (  1 <= i₅
                                                              && i₅ < i₁₃ + 1
                                                               ==> i₅ <= CELLCOUNT₁₁ / 5)))
                              &&   i₁₃ <= CELLCOUNT₁₁ / 5
                                ||   0 <= 0
                                  && 0 <= CELLCOUNT₁₁
                                  && (forall i₉: int ::
                                        (  0 <= i₉
                                          && i₉ < 0
                                           ==> i₉ < CELLCOUNT₁₁))
                                  && (forall i₁₄: int ::
                                        (  0 <= i₁₄
                                          && i₁₄ <= CELLCOUNT₁₁
                                          && (forall i₉: int ::
                                                (  0 <= i₉
                                                  && i₉ < i₁₄
                                                   ==> i₉ < CELLCOUNT₁₁))
                                           ==> (i₁₄ < CELLCOUNT₁₁
                                             ==> MINVAL <= volArray₁₂[i₁₄]
                                                || volArray₁₂[i₁₄] == 0
                                              && 0 <= i₁₄ + 1
                                              && i₁₄ + 1 <= CELLCOUNT₁₁
                                              && (forall i₉: int ::
                                                    (  0 <= i₉
                                                      && i₉ < i₁₄ + 1
                                                       ==> i₉ < CELLCOUNT₁₁))))))))))));

