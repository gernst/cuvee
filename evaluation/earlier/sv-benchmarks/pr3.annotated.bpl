data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall CELLCOUNT₁₁: int ::
          (true
             ==> (1 < CELLCOUNT₁₁
                 ==> (forall MINVAL: int ::
                      (forall volArray: [int]int ::
                              (CELLCOUNT₁₁ % 3 != 0
                                 ==> true)
                              && (!(CELLCOUNT₁₁ % 3 != 0
                              )
                                 ==> true
                                  && (CELLCOUNT₁₁ % 3 == 0
                                     ==> true
                                      && 1 <= 1
                                      && 1 <= 1 + CELLCOUNT₁₁ / 3
                                      && (forall x₆: int ::
                                            ((exists i₅: int ::
                                                  if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1)
                                               ==> (exists i₅: int ::
                                                        MINVAL <= 1
                                                        && MINVAL <= 3
                                                        && MINVAL <= 7
                                                        && i₅ <= CELLCOUNT₁₁ / 3
                                                        && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 7)
                                                || (exists i₅: int ::
                                                        MINVAL <= 1
                                                        && MINVAL <= 3
                                                        && !(MINVAL <= 7
                                                        )
                                                        && i₅ <= CELLCOUNT₁₁ / 3
                                                        && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0)
                                                || (exists i₅: int ::
                                                        MINVAL <= 1
                                                        && !(MINVAL <= 3
                                                        )
                                                        && MINVAL <= 7
                                                        && i₅ <= CELLCOUNT₁₁ / 3
                                                        && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 7)
                                                || (exists i₅: int ::
                                                        MINVAL <= 1
                                                        && !(MINVAL <= 3
                                                        )
                                                        && !(MINVAL <= 7
                                                        )
                                                        && i₅ <= CELLCOUNT₁₁ / 3
                                                        && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0)
                                                || (exists i₅: int ::
                                                        !(MINVAL <= 1
                                                        )
                                                        && MINVAL <= 3
                                                        && MINVAL <= 7
                                                        && i₅ <= CELLCOUNT₁₁ / 3
                                                        && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 7)
                                                || (exists i₅: int ::
                                                        !(MINVAL <= 1
                                                        )
                                                        && MINVAL <= 3
                                                        && !(MINVAL <= 7
                                                        )
                                                        && i₅ <= CELLCOUNT₁₁ / 3
                                                        && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0)
                                                || (exists i₅: int ::
                                                        !(MINVAL <= 1
                                                        )
                                                        && !(MINVAL <= 3
                                                        )
                                                        && MINVAL <= 7
                                                        && i₅ <= CELLCOUNT₁₁ / 3
                                                        && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 7)
                                                || (exists i₅: int ::
                                                        !(MINVAL <= 1
                                                        )
                                                        && !(MINVAL <= 3
                                                        )
                                                        && !(MINVAL <= 7
                                                        )
                                                        && i₅ <= CELLCOUNT₁₁ / 3
                                                        && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1 && volArray[x₆] == 0)))
                                      && (forall x₆: int ::
                                            (!((exists i₅: int ::
                                                  if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < 1)
                                            )
                                               ==> volArray[x₆] == volArray[x₆]))
                                      && (forall i₅: int ::
                                            (  i₅ <= i₅
                                              && 1 <= i₅
                                              && i₅ < 1
                                               ==> i₅ <= CELLCOUNT₁₁ / 3))
                                      && (forall volArray₁₂: [int]int, i₁₃: int ::
                                            (  true
                                              && 1 <= i₁₃
                                              && i₁₃ <= 1 + CELLCOUNT₁₁ / 3
                                              && (forall x₆: int ::
                                                    ((exists i₅: int ::
                                                          if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃)
                                                       ==> (exists i₅: int ::
                                                                MINVAL <= 1
                                                                && MINVAL <= 3
                                                                && MINVAL <= 7
                                                                && i₅ <= CELLCOUNT₁₁ / 3
                                                                && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 7)
                                                        || (exists i₅: int ::
                                                                MINVAL <= 1
                                                                && MINVAL <= 3
                                                                && !(MINVAL <= 7
                                                                )
                                                                && i₅ <= CELLCOUNT₁₁ / 3
                                                                && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0)
                                                        || (exists i₅: int ::
                                                                MINVAL <= 1
                                                                && !(MINVAL <= 3
                                                                )
                                                                && MINVAL <= 7
                                                                && i₅ <= CELLCOUNT₁₁ / 3
                                                                && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 7)
                                                        || (exists i₅: int ::
                                                                MINVAL <= 1
                                                                && !(MINVAL <= 3
                                                                )
                                                                && !(MINVAL <= 7
                                                                )
                                                                && i₅ <= CELLCOUNT₁₁ / 3
                                                                && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0)
                                                        || (exists i₅: int ::
                                                                !(MINVAL <= 1
                                                                )
                                                                && MINVAL <= 3
                                                                && MINVAL <= 7
                                                                && i₅ <= CELLCOUNT₁₁ / 3
                                                                && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 7)
                                                        || (exists i₅: int ::
                                                                !(MINVAL <= 1
                                                                )
                                                                && MINVAL <= 3
                                                                && !(MINVAL <= 7
                                                                )
                                                                && i₅ <= CELLCOUNT₁₁ / 3
                                                                && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0)
                                                        || (exists i₅: int ::
                                                                !(MINVAL <= 1
                                                                )
                                                                && !(MINVAL <= 3
                                                                )
                                                                && MINVAL <= 7
                                                                && i₅ <= CELLCOUNT₁₁ / 3
                                                                && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 7)
                                                        || (exists i₅: int ::
                                                                !(MINVAL <= 1
                                                                )
                                                                && !(MINVAL <= 3
                                                                )
                                                                && !(MINVAL <= 7
                                                                )
                                                                && i₅ <= CELLCOUNT₁₁ / 3
                                                                && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 0)))
                                              && (forall x₆: int ::
                                                    (!((exists i₅: int ::
                                                          if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃)
                                                    )
                                                       ==> volArray₁₂[x₆] == volArray[x₆]))
                                              && (forall i₅: int ::
                                                    (  i₅ <= i₅
                                                      && 1 <= i₅
                                                      && i₅ < i₁₃
                                                       ==> i₅ <= CELLCOUNT₁₁ / 3))
                                               ==> (i₁₃ <= CELLCOUNT₁₁ / 3
                                                   ==> (MINVAL <= 7
                                                       ==> (MINVAL <= 3
                                                           ==> (MINVAL <= 1
                                                               ==> true
                                                                && 1 <= i₁₃ + 1
                                                                && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 3
                                                                && (forall x₆: int ::
                                                                      ((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                         ==> (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0)))
                                                                && (forall x₆: int ::
                                                                      (!((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                      )
                                                                         ==> volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == volArray[x₆]))
                                                                && (forall i₅: int ::
                                                                      (  i₅ <= i₅
                                                                        && 1 <= i₅
                                                                        && i₅ < i₁₃ + 1
                                                                         ==> i₅ <= CELLCOUNT₁₁ / 3))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(MINVAL <= 1
                                                            )
                                                               ==> true
                                                                && 1 <= i₁₃ + 1
                                                                && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 3
                                                                && (forall x₆: int ::
                                                                      ((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                         ==> (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0)))
                                                                && (forall x₆: int ::
                                                                      (!((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                      )
                                                                         ==> volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == volArray[x₆]))
                                                                && (forall i₅: int ::
                                                                      (  i₅ <= i₅
                                                                        && 1 <= i₅
                                                                        && i₅ < i₁₃ + 1
                                                                         ==> i₅ <= CELLCOUNT₁₁ / 3))
                                                                && true
                                                                && (true
                                                                   ==> true)))
                                                        && (!(MINVAL <= 3
                                                        )
                                                           ==> (MINVAL <= 1
                                                               ==> true
                                                                && 1 <= i₁₃ + 1
                                                                && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 3
                                                                && (forall x₆: int ::
                                                                      ((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                         ==> (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0)))
                                                                && (forall x₆: int ::
                                                                      (!((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                      )
                                                                         ==> volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == volArray[x₆]))
                                                                && (forall i₅: int ::
                                                                      (  i₅ <= i₅
                                                                        && 1 <= i₅
                                                                        && i₅ < i₁₃ + 1
                                                                         ==> i₅ <= CELLCOUNT₁₁ / 3))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(MINVAL <= 1
                                                            )
                                                               ==> true
                                                                && 1 <= i₁₃ + 1
                                                                && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 3
                                                                && (forall x₆: int ::
                                                                      ((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                         ==> (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0)))
                                                                && (forall x₆: int ::
                                                                      (!((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                      )
                                                                         ==> volArray₁₂[i₁₃ * 3 - 3 := 7][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == volArray[x₆]))
                                                                && (forall i₅: int ::
                                                                      (  i₅ <= i₅
                                                                        && 1 <= i₅
                                                                        && i₅ < i₁₃ + 1
                                                                         ==> i₅ <= CELLCOUNT₁₁ / 3))
                                                                && true
                                                                && (true
                                                                   ==> true))))
                                                    && (!(MINVAL <= 7
                                                    )
                                                       ==> (MINVAL <= 3
                                                           ==> (MINVAL <= 1
                                                               ==> true
                                                                && 1 <= i₁₃ + 1
                                                                && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 3
                                                                && (forall x₆: int ::
                                                                      ((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                         ==> (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == 0)))
                                                                && (forall x₆: int ::
                                                                      (!((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                      )
                                                                         ==> volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 1][x₆] == volArray[x₆]))
                                                                && (forall i₅: int ::
                                                                      (  i₅ <= i₅
                                                                        && 1 <= i₅
                                                                        && i₅ < i₁₃ + 1
                                                                         ==> i₅ <= CELLCOUNT₁₁ / 3))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(MINVAL <= 1
                                                            )
                                                               ==> true
                                                                && 1 <= i₁₃ + 1
                                                                && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 3
                                                                && (forall x₆: int ::
                                                                      ((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                         ==> (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == 0)))
                                                                && (forall x₆: int ::
                                                                      (!((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                      )
                                                                         ==> volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 3][i₁₃ * 3 - 1 := 0][x₆] == volArray[x₆]))
                                                                && (forall i₅: int ::
                                                                      (  i₅ <= i₅
                                                                        && 1 <= i₅
                                                                        && i₅ < i₁₃ + 1
                                                                         ==> i₅ <= CELLCOUNT₁₁ / 3))
                                                                && true
                                                                && (true
                                                                   ==> true)))
                                                        && (!(MINVAL <= 3
                                                        )
                                                           ==> (MINVAL <= 1
                                                               ==> true
                                                                && 1 <= i₁₃ + 1
                                                                && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 3
                                                                && (forall x₆: int ::
                                                                      ((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                         ==> (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == 0)))
                                                                && (forall x₆: int ::
                                                                      (!((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                      )
                                                                         ==> volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 1][x₆] == volArray[x₆]))
                                                                && (forall i₅: int ::
                                                                      (  i₅ <= i₅
                                                                        && 1 <= i₅
                                                                        && i₅ < i₁₃ + 1
                                                                         ==> i₅ <= CELLCOUNT₁₁ / 3))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(MINVAL <= 1
                                                            )
                                                               ==> true
                                                                && 1 <= i₁₃ + 1
                                                                && i₁₃ + 1 <= 1 + CELLCOUNT₁₁ / 3
                                                                && (forall x₆: int ::
                                                                      ((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                         ==> (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  MINVAL <= 1
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && MINVAL <= 3
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 3 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && MINVAL <= 7
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 7)
                                                                          || (exists i₅: int ::
                                                                                  !(MINVAL <= 1
                                                                                  )
                                                                                  && !(MINVAL <= 3
                                                                                  )
                                                                                  && !(MINVAL <= 7
                                                                                  )
                                                                                  && i₅ <= CELLCOUNT₁₁ / 3
                                                                                  && if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1 && volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == 0)))
                                                                && (forall x₆: int ::
                                                                      (!((exists i₅: int ::
                                                                            if(x₆ == -1 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else if(x₆ == -2 + 3 * i₅) then 1 <= i₅ && i₅ < i₁₃ + 1 else x₆ == -3 + 3 * i₅ && 1 <= i₅ && i₅ < i₁₃ + 1)
                                                                      )
                                                                         ==> volArray₁₂[i₁₃ * 3 - 3 := 0][i₁₃ * 3 - 2 := 0][i₁₃ * 3 - 1 := 0][x₆] == volArray[x₆]))
                                                                && (forall i₅: int ::
                                                                      (  i₅ <= i₅
                                                                        && 1 <= i₅
                                                                        && i₅ < i₁₃ + 1
                                                                         ==> i₅ <= CELLCOUNT₁₁ / 3))
                                                                && true
                                                                && (true
                                                                   ==> true)))))
                                                && (!(i₁₃ <= CELLCOUNT₁₁ / 3
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 0 <= 0
                                                        && 0 <= CELLCOUNT₁₁
                                                        && (forall i₉: int ::
                                                              (  i₉ <= i₉
                                                                && 0 <= i₉
                                                                && i₉ < 0
                                                                 ==> i₉ < CELLCOUNT₁₁))
                                                        && (forall i₁₄: int ::
                                                              (  true
                                                                && 0 <= i₁₄
                                                                && i₁₄ <= CELLCOUNT₁₁
                                                                && (forall i₉: int ::
                                                                      (  i₉ <= i₉
                                                                        && 0 <= i₉
                                                                        && i₉ < i₁₄
                                                                         ==> i₉ < CELLCOUNT₁₁))
                                                                 ==> (i₁₄ < CELLCOUNT₁₁
                                                                     ==> MINVAL <= volArray₁₂[i₁₄]
                                                                        || volArray₁₂[i₁₄] == 0
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= i₁₄ + 1
                                                                          && i₁₄ + 1 <= CELLCOUNT₁₁
                                                                          && (forall i₉: int ::
                                                                                (  i₉ <= i₉
                                                                                  && 0 <= i₉
                                                                                  && i₉ < i₁₄ + 1
                                                                                   ==> i₉ < CELLCOUNT₁₁))
                                                                          && true
                                                                          && (true
                                                                             ==> true)))
                                                                  && (!(i₁₄ < CELLCOUNT₁₁
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true)))))))))))))
              && (!(1 < CELLCOUNT₁₁
              )
                 ==> true))));

