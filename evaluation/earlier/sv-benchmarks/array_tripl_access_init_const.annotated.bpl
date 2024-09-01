data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
        true
        && 0 <= 0
        && 0 <= 1 + 100000
        && (forall x₄: int ::
              ((exists i₃: int ::
                    if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < 0 else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < 0 else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < 0)
                 ==> (exists i₃: int ::
                        i₃ <= 100000
                        && if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < 0 && a[x₄] == 0 else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < 0 && a[x₄] == 0 else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < 0 && a[x₄] == 0)))
        && (forall x₄: int ::
              (!((exists i₃: int ::
                    if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < 0 else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < 0 else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < 0)
              )
                 ==> a[x₄] == a[x₄]))
        && (forall i₃: int ::
              (  i₃ <= i₃
                && 0 <= i₃
                && i₃ < 0
                 ==> i₃ <= 100000))
        && (forall a₉: [int]int, i₁₀: int ::
              (  true
                && 0 <= i₁₀
                && i₁₀ <= 1 + 100000
                && (forall x₄: int ::
                      ((exists i₃: int ::
                            if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < i₁₀)
                         ==> (exists i₃: int ::
                                i₃ <= 100000
                                && if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ && a₉[x₄] == 0 else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ && a₉[x₄] == 0 else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < i₁₀ && a₉[x₄] == 0)))
                && (forall x₄: int ::
                      (!((exists i₃: int ::
                            if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < i₁₀)
                      )
                         ==> a₉[x₄] == a[x₄]))
                && (forall i₃: int ::
                      (  i₃ <= i₃
                        && 0 <= i₃
                        && i₃ < i₁₀
                         ==> i₃ <= 100000))
                 ==> (i₁₀ <= 100000
                     ==> true
                      && 0 <= i₁₀ + 1
                      && i₁₀ + 1 <= 1 + 100000
                      && (forall x₄: int ::
                            ((exists i₃: int ::
                                  if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ + 1 else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ + 1 else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < i₁₀ + 1)
                               ==> (exists i₃: int ::
                                      i₃ <= 100000
                                      && if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ + 1 && a₉[3 * i₁₀ := 0][3 * i₁₀ + 1 := 0][3 * i₁₀ + 2 := 0][x₄] == 0 else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ + 1 && a₉[3 * i₁₀ := 0][3 * i₁₀ + 1 := 0][3 * i₁₀ + 2 := 0][x₄] == 0 else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < i₁₀ + 1 && a₉[3 * i₁₀ := 0][3 * i₁₀ + 1 := 0][3 * i₁₀ + 2 := 0][x₄] == 0)))
                      && (forall x₄: int ::
                            (!((exists i₃: int ::
                                  if(x₄ == 2 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ + 1 else if(x₄ == 1 + 3 * i₃) then 0 <= i₃ && i₃ < i₁₀ + 1 else x₄ == 3 * i₃ && 0 <= i₃ && i₃ < i₁₀ + 1)
                            )
                               ==> a₉[3 * i₁₀ := 0][3 * i₁₀ + 1 := 0][3 * i₁₀ + 2 := 0][x₄] == a[x₄]))
                      && (forall i₃: int ::
                            (  i₃ <= i₃
                              && 0 <= i₃
                              && i₃ < i₁₀ + 1
                               ==> i₃ <= 100000))
                      && true
                      && (true
                         ==> true))
                  && (!(i₁₀ <= 100000
                  )
                     ==> true
                      && (true
                         ==> true
                          && 0 <= 0
                          && 0 <= 1 + 3 * 100000
                          && (forall i₇: int ::
                                (  i₇ <= i₇
                                  && 0 <= i₇
                                  && i₇ < 0
                                   ==> i₇ <= 3 * 100000))
                          && (forall i₁₁: int ::
                                (  true
                                  && 0 <= i₁₁
                                  && i₁₁ <= 1 + 3 * 100000
                                  && (forall i₇: int ::
                                        (  i₇ <= i₇
                                          && 0 <= i₇
                                          && i₇ < i₁₁
                                           ==> i₇ <= 3 * 100000))
                                   ==> (i₁₁ <= 3 * 100000
                                       ==> 0 <= a₉[i₁₁]
                                        && (true
                                           ==> true
                                            && 0 <= i₁₁ + 1
                                            && i₁₁ + 1 <= 1 + 3 * 100000
                                            && (forall i₇: int ::
                                                  (  i₇ <= i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₁ + 1
                                                     ==> i₇ <= 3 * 100000))
                                            && true
                                            && (true
                                               ==> true)))
                                    && (!(i₁₁ <= 3 * 100000
                                    )
                                       ==> true
                                        && (true
                                           ==> true)))))))));

