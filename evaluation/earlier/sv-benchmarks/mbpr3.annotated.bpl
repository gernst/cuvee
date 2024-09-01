data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall CELLCOUNT₁₈: int ::
          (true
             ==> (1 < CELLCOUNT₁₈
                 ==> (forall volArray: [int]int ::
                        (CELLCOUNT₁₈ % 3 != 0
                           ==> true)
                        && (!(CELLCOUNT₁₈ % 3 != 0
                        )
                           ==> true
                            && (CELLCOUNT₁₈ % 3 == 0
                               ==> true
                                && 1 <= 1
                                && 1 <= 1 + CELLCOUNT₁₈ / 3
                                && (forall x₅: int ::
                                      ((exists i₄: int ::
                                            if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < 1 else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < 1 else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < 1)
                                         ==> (exists i₄: int ::
                                                  2 <= 7
                                                  && i₄ <= CELLCOUNT₁₈ / 3
                                                  && if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < 1 && volArray[x₅] == volArray[-3 + 3 * i₄ := 7][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < 1 && volArray[x₅] == volArray[-3 + 3 * i₄ := 7][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < 1 && volArray[x₅] == 7)
                                          || (exists i₄: int ::
                                                  !(2 <= 7
                                                  )
                                                  && i₄ <= CELLCOUNT₁₈ / 3
                                                  && if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < 1 && volArray[x₅] == volArray[-3 + 3 * i₄ := 0][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < 1 && volArray[x₅] == volArray[-3 + 3 * i₄ := 0][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < 1 && volArray[x₅] == 0)))
                                && (forall x₅: int ::
                                      (!((exists i₄: int ::
                                            if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < 1 else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < 1 else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < 1)
                                      )
                                         ==> volArray[x₅] == volArray[x₅]))
                                && (forall i₄: int ::
                                      (  i₄ <= i₄
                                        && 1 <= i₄
                                        && i₄ < 1
                                         ==> i₄ <= CELLCOUNT₁₈ / 3))
                                && (forall volArray₁₉: [int]int, i₂₀: int ::
                                      (  true
                                        && 1 <= i₂₀
                                        && i₂₀ <= 1 + CELLCOUNT₁₈ / 3
                                        && (forall x₅: int ::
                                              ((exists i₄: int ::
                                                    if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀)
                                                 ==> (exists i₄: int ::
                                                          2 <= 7
                                                          && i₄ <= CELLCOUNT₁₈ / 3
                                                          && if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ && volArray₁₉[x₅] == volArray₁₉[-3 + 3 * i₄ := 7][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ && volArray₁₉[x₅] == volArray₁₉[-3 + 3 * i₄ := 7][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ && volArray₁₉[x₅] == 7)
                                                  || (exists i₄: int ::
                                                          !(2 <= 7
                                                          )
                                                          && i₄ <= CELLCOUNT₁₈ / 3
                                                          && if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ && volArray₁₉[x₅] == volArray₁₉[-3 + 3 * i₄ := 0][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ && volArray₁₉[x₅] == volArray₁₉[-3 + 3 * i₄ := 0][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ && volArray₁₉[x₅] == 0)))
                                        && (forall x₅: int ::
                                              (!((exists i₄: int ::
                                                    if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀)
                                              )
                                                 ==> volArray₁₉[x₅] == volArray[x₅]))
                                        && (forall i₄: int ::
                                              (  i₄ <= i₄
                                                && 1 <= i₄
                                                && i₄ < i₂₀
                                                 ==> i₄ <= CELLCOUNT₁₈ / 3))
                                         ==> (i₂₀ <= CELLCOUNT₁₈ / 3
                                             ==> (2 <= 7
                                                 ==> true
                                                  && 1 <= i₂₀ + 1
                                                  && i₂₀ + 1 <= 1 + CELLCOUNT₁₈ / 3
                                                  && (forall x₅: int ::
                                                        ((exists i₄: int ::
                                                              if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ + 1)
                                                           ==> (exists i₄: int ::
                                                                    2 <= 7
                                                                    && i₄ <= CELLCOUNT₁₈ / 3
                                                                    && if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][-3 + 3 * i₄ := 7][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][-3 + 3 * i₄ := 7][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == 7)
                                                            || (exists i₄: int ::
                                                                    !(2 <= 7
                                                                    )
                                                                    && i₄ <= CELLCOUNT₁₈ / 3
                                                                    && if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][-3 + 3 * i₄ := 0][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][-3 + 3 * i₄ := 0][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == 0)))
                                                  && (forall x₅: int ::
                                                        (!((exists i₄: int ::
                                                              if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ + 1)
                                                        )
                                                           ==> volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 7][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray[x₅]))
                                                  && (forall i₄: int ::
                                                        (  i₄ <= i₄
                                                          && 1 <= i₄
                                                          && i₄ < i₂₀ + 1
                                                           ==> i₄ <= CELLCOUNT₁₈ / 3))
                                                  && true
                                                  && (true
                                                     ==> true))
                                              && (!(2 <= 7
                                              )
                                                 ==> true
                                                  && 1 <= i₂₀ + 1
                                                  && i₂₀ + 1 <= 1 + CELLCOUNT₁₈ / 3
                                                  && (forall x₅: int ::
                                                        ((exists i₄: int ::
                                                              if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ + 1)
                                                           ==> (exists i₄: int ::
                                                                    2 <= 7
                                                                    && i₄ <= CELLCOUNT₁₈ / 3
                                                                    && if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][-3 + 3 * i₄ := 7][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][-3 + 3 * i₄ := 7][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == 7)
                                                            || (exists i₄: int ::
                                                                    !(2 <= 7
                                                                    )
                                                                    && i₄ <= CELLCOUNT₁₈ / 3
                                                                    && if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][-3 + 3 * i₄ := 0][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][-3 + 3 * i₄ := 0][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ + 1 && volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == 0)))
                                                  && (forall x₅: int ::
                                                        (!((exists i₄: int ::
                                                              if(x₅ == -1 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 else if(x₅ == -2 + 3 * i₄) then 1 <= i₄ && i₄ < i₂₀ + 1 else x₅ == -3 + 3 * i₄ && 1 <= i₄ && i₄ < i₂₀ + 1)
                                                        )
                                                           ==> volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2 := volArray₁₉[i₂₀ * 3 - 3 := 0][i₂₀ * 3 - 2]][i₂₀ * 3 - 1]][x₅] == volArray[x₅]))
                                                  && (forall i₄: int ::
                                                        (  i₄ <= i₄
                                                          && 1 <= i₄
                                                          && i₄ < i₂₀ + 1
                                                           ==> i₄ <= CELLCOUNT₁₈ / 3))
                                                  && true
                                                  && (true
                                                     ==> true)))
                                          && (!(i₂₀ <= CELLCOUNT₁₈ / 3
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 1 <= 1
                                                  && 1 <= 1 + CELLCOUNT₁₈ / 3
                                                  && (forall x₉: int ::
                                                        ((exists i₈: int ::
                                                              if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < 1 else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < 1 else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < 1)
                                                           ==> (exists i₈: int ::
                                                                    2 <= 3
                                                                    && i₈ <= CELLCOUNT₁₈ / 3
                                                                    && if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < 1 && volArray₁₉[x₉] == volArray₁₉[-2 + 3 * i₈ := 3][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < 1 && volArray₁₉[x₉] == volArray₁₉[-2 + 3 * i₈ := 3][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < 1 && volArray₁₉[x₉] == 3)
                                                            || (exists i₈: int ::
                                                                    !(2 <= 3
                                                                    )
                                                                    && i₈ <= CELLCOUNT₁₈ / 3
                                                                    && if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < 1 && volArray₁₉[x₉] == volArray₁₉[-2 + 3 * i₈ := 0][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < 1 && volArray₁₉[x₉] == volArray₁₉[-2 + 3 * i₈ := 0][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < 1 && volArray₁₉[x₉] == 0)))
                                                  && (forall x₉: int ::
                                                        (!((exists i₈: int ::
                                                              if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < 1 else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < 1 else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < 1)
                                                        )
                                                           ==> volArray₁₉[x₉] == volArray₁₉[x₉]))
                                                  && (forall i₈: int ::
                                                        (  i₈ <= i₈
                                                          && 1 <= i₈
                                                          && i₈ < 1
                                                           ==> i₈ <= CELLCOUNT₁₈ / 3))
                                                  && (forall volArray₂₁: [int]int, i₂₂: int ::
                                                        (  true
                                                          && 1 <= i₂₂
                                                          && i₂₂ <= 1 + CELLCOUNT₁₈ / 3
                                                          && (forall x₉: int ::
                                                                ((exists i₈: int ::
                                                                      if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂)
                                                                   ==> (exists i₈: int ::
                                                                            2 <= 3
                                                                            && i₈ <= CELLCOUNT₁₈ / 3
                                                                            && if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ && volArray₂₁[x₉] == volArray₂₁[-2 + 3 * i₈ := 3][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ && volArray₂₁[x₉] == volArray₂₁[-2 + 3 * i₈ := 3][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ && volArray₂₁[x₉] == 3)
                                                                    || (exists i₈: int ::
                                                                            !(2 <= 3
                                                                            )
                                                                            && i₈ <= CELLCOUNT₁₈ / 3
                                                                            && if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ && volArray₂₁[x₉] == volArray₂₁[-2 + 3 * i₈ := 0][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ && volArray₂₁[x₉] == volArray₂₁[-2 + 3 * i₈ := 0][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ && volArray₂₁[x₉] == 0)))
                                                          && (forall x₉: int ::
                                                                (!((exists i₈: int ::
                                                                      if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂)
                                                                )
                                                                   ==> volArray₂₁[x₉] == volArray₁₉[x₉]))
                                                          && (forall i₈: int ::
                                                                (  i₈ <= i₈
                                                                  && 1 <= i₈
                                                                  && i₈ < i₂₂
                                                                   ==> i₈ <= CELLCOUNT₁₈ / 3))
                                                           ==> (i₂₂ <= CELLCOUNT₁₈ / 3
                                                               ==> (2 <= 3
                                                                   ==> true
                                                                    && 1 <= i₂₂ + 1
                                                                    && i₂₂ + 1 <= 1 + CELLCOUNT₁₈ / 3
                                                                    && (forall x₉: int ::
                                                                          ((exists i₈: int ::
                                                                                if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ + 1)
                                                                             ==> (exists i₈: int ::
                                                                                      2 <= 3
                                                                                      && i₈ <= CELLCOUNT₁₈ / 3
                                                                                      && if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][-2 + 3 * i₈ := 3][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][-2 + 3 * i₈ := 3][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == 3)
                                                                              || (exists i₈: int ::
                                                                                      !(2 <= 3
                                                                                      )
                                                                                      && i₈ <= CELLCOUNT₁₈ / 3
                                                                                      && if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][-2 + 3 * i₈ := 0][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][-2 + 3 * i₈ := 0][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == 0)))
                                                                    && (forall x₉: int ::
                                                                          (!((exists i₈: int ::
                                                                                if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ + 1)
                                                                          )
                                                                             ==> volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 3][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₁₉[x₉]))
                                                                    && (forall i₈: int ::
                                                                          (  i₈ <= i₈
                                                                            && 1 <= i₈
                                                                            && i₈ < i₂₂ + 1
                                                                             ==> i₈ <= CELLCOUNT₁₈ / 3))
                                                                    && true
                                                                    && (true
                                                                       ==> true))
                                                                && (!(2 <= 3
                                                                )
                                                                   ==> true
                                                                    && 1 <= i₂₂ + 1
                                                                    && i₂₂ + 1 <= 1 + CELLCOUNT₁₈ / 3
                                                                    && (forall x₉: int ::
                                                                          ((exists i₈: int ::
                                                                                if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ + 1)
                                                                             ==> (exists i₈: int ::
                                                                                      2 <= 3
                                                                                      && i₈ <= CELLCOUNT₁₈ / 3
                                                                                      && if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][-2 + 3 * i₈ := 3][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][-2 + 3 * i₈ := 3][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == 3)
                                                                              || (exists i₈: int ::
                                                                                      !(2 <= 3
                                                                                      )
                                                                                      && i₈ <= CELLCOUNT₁₈ / 3
                                                                                      && if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][-2 + 3 * i₈ := 0][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][-2 + 3 * i₈ := 0][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ + 1 && volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == 0)))
                                                                    && (forall x₉: int ::
                                                                          (!((exists i₈: int ::
                                                                                if(x₉ == -1 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 else if(x₉ == -3 + 3 * i₈) then 1 <= i₈ && i₈ < i₂₂ + 1 else x₉ == -2 + 3 * i₈ && 1 <= i₈ && i₈ < i₂₂ + 1)
                                                                          )
                                                                             ==> volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3 := volArray₂₁[i₂₂ * 3 - 2 := 0][i₂₂ * 3 - 3]][i₂₂ * 3 - 1]][x₉] == volArray₁₉[x₉]))
                                                                    && (forall i₈: int ::
                                                                          (  i₈ <= i₈
                                                                            && 1 <= i₈
                                                                            && i₈ < i₂₂ + 1
                                                                             ==> i₈ <= CELLCOUNT₁₈ / 3))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(i₂₂ <= CELLCOUNT₁₈ / 3
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 1 <= 1
                                                                    && 1 <= 1 + CELLCOUNT₁₈ / 3
                                                                    && (forall x₁₃: int ::
                                                                          ((exists i₁₂: int ::
                                                                                if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < 1 else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < 1 else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < 1)
                                                                             ==> (exists i₁₂: int ::
                                                                                      2 <= 1
                                                                                      && i₁₂ <= CELLCOUNT₁₈ / 3
                                                                                      && if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < 1 && volArray₂₁[x₁₃] == volArray₂₁[-1 + 3 * i₁₂ := 1][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < 1 && volArray₂₁[x₁₃] == volArray₂₁[-1 + 3 * i₁₂ := 1][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < 1 && volArray₂₁[x₁₃] == 1)
                                                                              || (exists i₁₂: int ::
                                                                                      !(2 <= 1
                                                                                      )
                                                                                      && i₁₂ <= CELLCOUNT₁₈ / 3
                                                                                      && if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < 1 && volArray₂₁[x₁₃] == volArray₂₁[-1 + 3 * i₁₂ := 0][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < 1 && volArray₂₁[x₁₃] == volArray₂₁[-1 + 3 * i₁₂ := 0][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < 1 && volArray₂₁[x₁₃] == 0)))
                                                                    && (forall x₁₃: int ::
                                                                          (!((exists i₁₂: int ::
                                                                                if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < 1 else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < 1 else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < 1)
                                                                          )
                                                                             ==> volArray₂₁[x₁₃] == volArray₂₁[x₁₃]))
                                                                    && (forall i₁₂: int ::
                                                                          (  i₁₂ <= i₁₂
                                                                            && 1 <= i₁₂
                                                                            && i₁₂ < 1
                                                                             ==> i₁₂ <= CELLCOUNT₁₈ / 3))
                                                                    && (forall volArray₂₃: [int]int, i₂₄: int ::
                                                                          (  true
                                                                            && 1 <= i₂₄
                                                                            && i₂₄ <= 1 + CELLCOUNT₁₈ / 3
                                                                            && (forall x₁₃: int ::
                                                                                  ((exists i₁₂: int ::
                                                                                        if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄)
                                                                                     ==> (exists i₁₂: int ::
                                                                                              2 <= 1
                                                                                              && i₁₂ <= CELLCOUNT₁₈ / 3
                                                                                              && if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ && volArray₂₃[x₁₃] == volArray₂₃[-1 + 3 * i₁₂ := 1][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ && volArray₂₃[x₁₃] == volArray₂₃[-1 + 3 * i₁₂ := 1][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ && volArray₂₃[x₁₃] == 1)
                                                                                      || (exists i₁₂: int ::
                                                                                              !(2 <= 1
                                                                                              )
                                                                                              && i₁₂ <= CELLCOUNT₁₈ / 3
                                                                                              && if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ && volArray₂₃[x₁₃] == volArray₂₃[-1 + 3 * i₁₂ := 0][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ && volArray₂₃[x₁₃] == volArray₂₃[-1 + 3 * i₁₂ := 0][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ && volArray₂₃[x₁₃] == 0)))
                                                                            && (forall x₁₃: int ::
                                                                                  (!((exists i₁₂: int ::
                                                                                        if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄)
                                                                                  )
                                                                                     ==> volArray₂₃[x₁₃] == volArray₂₁[x₁₃]))
                                                                            && (forall i₁₂: int ::
                                                                                  (  i₁₂ <= i₁₂
                                                                                    && 1 <= i₁₂
                                                                                    && i₁₂ < i₂₄
                                                                                     ==> i₁₂ <= CELLCOUNT₁₈ / 3))
                                                                             ==> (i₂₄ <= CELLCOUNT₁₈ / 3
                                                                                 ==> (2 <= 1
                                                                                     ==> true
                                                                                      && 1 <= i₂₄ + 1
                                                                                      && i₂₄ + 1 <= 1 + CELLCOUNT₁₈ / 3
                                                                                      && (forall x₁₃: int ::
                                                                                            ((exists i₁₂: int ::
                                                                                                  if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ + 1)
                                                                                               ==> (exists i₁₂: int ::
                                                                                                        2 <= 1
                                                                                                        && i₁₂ <= CELLCOUNT₁₈ / 3
                                                                                                        && if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][-1 + 3 * i₁₂ := 1][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][-1 + 3 * i₁₂ := 1][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == 1)
                                                                                                || (exists i₁₂: int ::
                                                                                                        !(2 <= 1
                                                                                                        )
                                                                                                        && i₁₂ <= CELLCOUNT₁₈ / 3
                                                                                                        && if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][-1 + 3 * i₁₂ := 0][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][-1 + 3 * i₁₂ := 0][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == 0)))
                                                                                      && (forall x₁₃: int ::
                                                                                            (!((exists i₁₂: int ::
                                                                                                  if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ + 1)
                                                                                            )
                                                                                               ==> volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 1][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₁[x₁₃]))
                                                                                      && (forall i₁₂: int ::
                                                                                            (  i₁₂ <= i₁₂
                                                                                              && 1 <= i₁₂
                                                                                              && i₁₂ < i₂₄ + 1
                                                                                               ==> i₁₂ <= CELLCOUNT₁₈ / 3))
                                                                                      && true
                                                                                      && (true
                                                                                         ==> true))
                                                                                  && (!(2 <= 1
                                                                                  )
                                                                                     ==> true
                                                                                      && 1 <= i₂₄ + 1
                                                                                      && i₂₄ + 1 <= 1 + CELLCOUNT₁₈ / 3
                                                                                      && (forall x₁₃: int ::
                                                                                            ((exists i₁₂: int ::
                                                                                                  if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ + 1)
                                                                                               ==> (exists i₁₂: int ::
                                                                                                        2 <= 1
                                                                                                        && i₁₂ <= CELLCOUNT₁₈ / 3
                                                                                                        && if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][-1 + 3 * i₁₂ := 1][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][-1 + 3 * i₁₂ := 1][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == 1)
                                                                                                || (exists i₁₂: int ::
                                                                                                        !(2 <= 1
                                                                                                        )
                                                                                                        && i₁₂ <= CELLCOUNT₁₈ / 3
                                                                                                        && if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][-1 + 3 * i₁₂ := 0][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][-1 + 3 * i₁₂ := 0][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ + 1 && volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == 0)))
                                                                                      && (forall x₁₃: int ::
                                                                                            (!((exists i₁₂: int ::
                                                                                                  if(x₁₃ == -3 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 else if(x₁₃ == -2 + 3 * i₁₂) then 1 <= i₁₂ && i₁₂ < i₂₄ + 1 else x₁₃ == -1 + 3 * i₁₂ && 1 <= i₁₂ && i₁₂ < i₂₄ + 1)
                                                                                            )
                                                                                               ==> volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2 := volArray₂₃[i₂₄ * 3 - 1 := 0][i₂₄ * 3 - 2]][i₂₄ * 3 - 3]][x₁₃] == volArray₂₁[x₁₃]))
                                                                                      && (forall i₁₂: int ::
                                                                                            (  i₁₂ <= i₁₂
                                                                                              && 1 <= i₁₂
                                                                                              && i₁₂ < i₂₄ + 1
                                                                                               ==> i₁₂ <= CELLCOUNT₁₈ / 3))
                                                                                      && true
                                                                                      && (true
                                                                                         ==> true)))
                                                                              && (!(i₂₄ <= CELLCOUNT₁₈ / 3
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true
                                                                                      && 0 <= 0
                                                                                      && 0 <= CELLCOUNT₁₈
                                                                                      && (forall i₁₆: int ::
                                                                                            (  i₁₆ <= i₁₆
                                                                                              && 0 <= i₁₆
                                                                                              && i₁₆ < 0
                                                                                               ==> i₁₆ < CELLCOUNT₁₈))
                                                                                      && (forall i₂₅: int ::
                                                                                            (  true
                                                                                              && 0 <= i₂₅
                                                                                              && i₂₅ <= CELLCOUNT₁₈
                                                                                              && (forall i₁₆: int ::
                                                                                                    (  i₁₆ <= i₁₆
                                                                                                      && 0 <= i₁₆
                                                                                                      && i₁₆ < i₂₅
                                                                                                       ==> i₁₆ < CELLCOUNT₁₈))
                                                                                               ==> (i₂₅ < CELLCOUNT₁₈
                                                                                                   ==> 2 <= volArray₂₃[i₂₅]
                                                                                                      || volArray₂₃[i₂₅] == 0
                                                                                                    && (true
                                                                                                       ==> true
                                                                                                        && 0 <= i₂₅ + 1
                                                                                                        && i₂₅ + 1 <= CELLCOUNT₁₈
                                                                                                        && (forall i₁₆: int ::
                                                                                                              (  i₁₆ <= i₁₆
                                                                                                                && 0 <= i₁₆
                                                                                                                && i₁₆ < i₂₅ + 1
                                                                                                                 ==> i₁₆ < CELLCOUNT₁₈))
                                                                                                        && true
                                                                                                        && (true
                                                                                                           ==> true)))
                                                                                                && (!(i₂₅ < CELLCOUNT₁₈
                                                                                                )
                                                                                                   ==> true
                                                                                                    && (true
                                                                                                       ==> true))))))))))))))))))))
              && (!(1 < CELLCOUNT₁₈
              )
                 ==> true))));

