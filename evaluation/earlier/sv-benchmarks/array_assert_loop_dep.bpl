data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 0 <= i₃
                && i₃ < 0
                 ==> (exists i₃: int ::
                        i₃ < 100000
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < 0
                        && a[x₄] == 10)))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 0 <= i₃
                        && i₃ < 0)
                || a[x₄] == a[x₄])
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < 0
                 ==> i₃ < 100000))
        && (forall a₁₁: [int]int, i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ <= 100000
                && (forall x₄: int, i₃: int ::
                      (  x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₂
                         ==> (exists i₃: int ::
                                i₃ < 100000
                                && x₄ == i₃
                                && 0 <= i₃
                                && i₃ < i₁₂
                                && a₁₁[x₄] == 10)))
                && (forall x₄: int ::
                        (exists i₃: int ::
                                x₄ == i₃
                                && 0 <= i₃
                                && i₃ < i₁₂)
                        || a₁₁[x₄] == a[x₄])
                && (forall i₃: int ::
                      (  0 <= i₃
                        && i₃ < i₁₂
                         ==> i₃ < 100000))
                 ==> (i₁₂ < 100000
                     ==> 0 <= i₁₂ + 1
                      && i₁₂ + 1 <= 100000
                      && (forall x₄: int, i₃: int ::
                            (  x₄ == i₃
                              && 0 <= i₃
                              && i₃ < i₁₂ + 1
                               ==> (exists i₃: int ::
                                      i₃ < 100000
                                      && x₄ == i₃
                                      && 0 <= i₃
                                      && i₃ < i₁₂ + 1
                                      && a₁₁[i₁₂ := 10][x₄] == 10)))
                      && (forall x₄: int ::
                              (exists i₃: int ::
                                      x₄ == i₃
                                      && 0 <= i₃
                                      && i₃ < i₁₂ + 1)
                              || a₁₁[i₁₂ := 10][x₄] == a[x₄])
                      && (forall i₃: int ::
                            (  0 <= i₃
                              && i₃ < i₁₂ + 1
                               ==> i₃ < 100000)))
                  &&   i₁₂ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₈: int, i₇: int ::
                            (  x₈ == 1 + i₇
                              && 0 <= i₇
                              && i₇ < 0
                               ==> (exists i₇: int ::
                                    (1 + i₇ == 15000
                                       ==> false))))
                      && (forall x₈: int ::
                              (exists i₇: int ::
                                      x₈ == 1 + i₇
                                      && 0 <= i₇
                                      && i₇ < 0)
                              || a₁₁[x₈] == a₁₁[x₈])
                      && (forall i₇: int ::
                            (  0 <= i₇
                              && i₇ < 0
                               ==> i₇ < 100000))
                      && (forall a₁₃: [int]int, i₁₄: int ::
                            (  0 <= i₁₄
                              && i₁₄ <= 100000
                              && (forall x₈: int, i₇: int ::
                                    (  x₈ == 1 + i₇
                                      && 0 <= i₇
                                      && i₇ < i₁₄
                                       ==> (exists i₇: int ::
                                            (1 + i₇ == 15000
                                               ==> false))))
                              && (forall x₈: int ::
                                      (exists i₇: int ::
                                              x₈ == 1 + i₇
                                              && 0 <= i₇
                                              && i₇ < i₁₄)
                                      || a₁₃[x₈] == a₁₁[x₈])
                              && (forall i₇: int ::
                                    (  0 <= i₇
                                      && i₇ < i₁₄
                                       ==> i₇ < 100000))
                               ==> (i₁₄ < 100000
                                 ==> a₁₃[i₁₄] == 10
                                  &&   i₁₄ + 1 == 15000
                                    ||   0 <= i₁₄ + 1
                                      && i₁₄ + 1 <= 100000
                                      && (forall x₈: int, i₇: int ::
                                            (  x₈ == 1 + i₇
                                              && 0 <= i₇
                                              && i₇ < i₁₄ + 1
                                               ==> (exists i₇: int ::
                                                    (1 + i₇ == 15000
                                                       ==> false))))
                                      && (forall x₈: int ::
                                              (exists i₇: int ::
                                                      x₈ == 1 + i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₄ + 1)
                                              || a₁₃[i₁₄ + 1 := 20][x₈] == a₁₁[x₈])
                                      && (forall i₇: int ::
                                            (  0 <= i₇
                                              && i₇ < i₁₄ + 1
                                               ==> i₇ < 100000))
                                  && (i₁₄ + 1 == 15000
                                     ==> 0 <= i₁₄ + 1
                                      && i₁₄ + 1 <= 100000
                                      && (forall x₈: int, i₇: int ::
                                            (  x₈ == 1 + i₇
                                              && 0 <= i₇
                                              && i₇ < i₁₄ + 1
                                               ==> (exists i₇: int ::
                                                    (1 + i₇ == 15000
                                                       ==> false))))
                                      && (forall x₈: int ::
                                              (exists i₇: int ::
                                                      x₈ == 1 + i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₄ + 1)
                                              || a₁₃[x₈] == a₁₁[x₈])
                                      && (forall i₇: int ::
                                            (  0 <= i₇
                                              && i₇ < i₁₄ + 1
                                               ==> i₇ < 100000)))))))));

