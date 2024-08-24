data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
        1 <= 1
        && 1 <= 100000
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 1 <= i₃
                && i₃ < 1
                 ==> (exists i₃: int ::
                        i₃ < 100000
                        && x₄ == i₃
                        && 1 <= i₃
                        && i₃ < 1
                        && a[0 := 7][x₄] == 1 + a[0 := 7][-1 + i₃])))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 1 <= i₃
                        && i₃ < 1)
                || a[0 := 7][x₄] == a[0 := 7][x₄])
        && (forall i₃: int ::
              (  1 <= i₃
                && i₃ < 1
                 ==> i₃ < 100000))
        && (forall a₁₀: [int]int, i₁₁: int ::
              (  1 <= i₁₁
                && i₁₁ <= 100000
                && (forall x₄: int, i₃: int ::
                      (  x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₁
                         ==> (exists i₃: int ::
                                i₃ < 100000
                                && x₄ == i₃
                                && 1 <= i₃
                                && i₃ < i₁₁
                                && a₁₀[x₄] == 1 + a[0 := 7][-1 + i₃])))
                && (forall x₄: int ::
                        (exists i₃: int ::
                                x₄ == i₃
                                && 1 <= i₃
                                && i₃ < i₁₁)
                        || a₁₀[x₄] == a[0 := 7][x₄])
                && (forall i₃: int ::
                      (  1 <= i₃
                        && i₃ < i₁₁
                         ==> i₃ < 100000))
                 ==> (i₁₁ < 100000
                     ==> 1 <= i₁₁ + 1
                      && i₁₁ + 1 <= 100000
                      && (forall x₄: int, i₃: int ::
                            (  x₄ == i₃
                              && 1 <= i₃
                              && i₃ < i₁₁ + 1
                               ==> (exists i₃: int ::
                                      i₃ < 100000
                                      && x₄ == i₃
                                      && 1 <= i₃
                                      && i₃ < i₁₁ + 1
                                      && a₁₀[i₁₁ := a₁₀[i₁₁ - 1] + 1][x₄] == 1 + a[0 := 7][-1 + i₃])))
                      && (forall x₄: int ::
                              (exists i₃: int ::
                                      x₄ == i₃
                                      && 1 <= i₃
                                      && i₃ < i₁₁ + 1)
                              || a₁₀[i₁₁ := a₁₀[i₁₁ - 1] + 1][x₄] == a[0 := 7][x₄])
                      && (forall i₃: int ::
                            (  1 <= i₃
                              && i₃ < i₁₁ + 1
                               ==> i₃ < 100000)))
                  &&   i₁₁ < 100000
                    ||   1 <= 1
                      && 1 <= 100000
                      && (forall x₈: int ::
                            (  1 <= x₈
                              && x₈ < 1
                               ==> x₈ < 100000))
                      && (forall x₁₂: int ::
                            (  1 <= x₁₂
                              && x₁₂ <= 100000
                              && (forall x₈: int ::
                                    (  1 <= x₈
                                      && x₈ < x₁₂
                                       ==> x₈ < 100000))
                               ==> (x₁₂ < 100000
                                 ==> a₁₀[x₁₂ - 1] <= a₁₀[x₁₂]
                                  && 1 <= x₁₂ + 1
                                  && x₁₂ + 1 <= 100000
                                  && (forall x₈: int ::
                                        (  1 <= x₈
                                          && x₈ < x₁₂ + 1
                                           ==> x₈ < 100000))))))));

