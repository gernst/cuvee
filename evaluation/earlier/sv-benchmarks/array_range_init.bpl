data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var a: [int]int;

goal (forall a: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₃: int, i₂: int ::
              (  x₃ == i₂
                && 0 <= i₂
                && i₂ < 0
                 ==> (exists i₂: int ::
                          0 <= i₂
                          && i₂ <= 10000
                          && i₂ < 100000
                          && x₃ == i₂
                          && i₂ < 0
                          && a[x₃] == 10)
                  || (exists i₂: int ::
                        (  0 <= i₂
                          && i₂ <= 10000
                           ==> false))))
        && (forall x₃: int ::
                (exists i₂: int ::
                        x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0)
                || a[x₃] == a[x₃])
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < 0
                 ==> i₂ < 100000))
        && (forall a₈: [int]int, i₉: int ::
              (  0 <= i₉
                && i₉ <= 100000
                && (forall x₃: int, i₂: int ::
                      (  x₃ == i₂
                        && 0 <= i₂
                        && i₂ < i₉
                         ==> (exists i₂: int ::
                                  0 <= i₂
                                  && i₂ <= 10000
                                  && i₂ < 100000
                                  && x₃ == i₂
                                  && i₂ < i₉
                                  && a₈[x₃] == 10)
                          || (exists i₂: int ::
                                (  0 <= i₂
                                  && i₂ <= 10000
                                   ==> false))))
                && (forall x₃: int ::
                        (exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₉)
                        || a₈[x₃] == a[x₃])
                && (forall i₂: int ::
                      (  0 <= i₂
                        && i₂ < i₉
                         ==> i₂ < 100000))
                 ==> (i₉ < 100000
                     ==> (  0 <= i₉
                        && i₉ <= 10000
                         ==> 0 <= i₉ + 1
                          && i₉ + 1 <= 100000
                          && (forall x₃: int, i₂: int ::
                                (  x₃ == i₂
                                  && 0 <= i₂
                                  && i₂ < i₉ + 1
                                   ==> (exists i₂: int ::
                                            0 <= i₂
                                            && i₂ <= 10000
                                            && i₂ < 100000
                                            && x₃ == i₂
                                            && i₂ < i₉ + 1
                                            && a₈[i₉ := 10][x₃] == 10)
                                    || (exists i₂: int ::
                                          (  0 <= i₂
                                            && i₂ <= 10000
                                             ==> false))))
                          && (forall x₃: int ::
                                  (exists i₂: int ::
                                          x₃ == i₂
                                          && 0 <= i₂
                                          && i₂ < i₉ + 1)
                                  || a₈[i₉ := 10][x₃] == a[x₃])
                          && (forall i₂: int ::
                                (  0 <= i₂
                                  && i₂ < i₉ + 1
                                   ==> i₂ < 100000)))
                      &&     0 <= i₉
                          && i₉ <= 10000
                        ||   0 <= i₉ + 1
                          && i₉ + 1 <= 100000
                          && (forall x₃: int, i₂: int ::
                                (  x₃ == i₂
                                  && 0 <= i₂
                                  && i₂ < i₉ + 1
                                   ==> (exists i₂: int ::
                                            0 <= i₂
                                            && i₂ <= 10000
                                            && i₂ < 100000
                                            && x₃ == i₂
                                            && i₂ < i₉ + 1
                                            && a₈[i₉ := 0][x₃] == 10)
                                    || (exists i₂: int ::
                                          (  0 <= i₂
                                            && i₂ <= 10000
                                             ==> false))))
                          && (forall x₃: int ::
                                  (exists i₂: int ::
                                          x₃ == i₂
                                          && 0 <= i₂
                                          && i₂ < i₉ + 1)
                                  || a₈[i₉ := 0][x₃] == a[x₃])
                          && (forall i₂: int ::
                                (  0 <= i₂
                                  && i₂ < i₉ + 1
                                   ==> i₂ < 100000)))
                  &&   i₉ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall i₆: int ::
                            (  0 <= i₆
                              && i₆ < 0
                               ==> i₆ < 100000))
                      && (forall i₁₀: int ::
                            (  0 <= i₁₀
                              && i₁₀ <= 100000
                              && (forall i₆: int ::
                                    (  0 <= i₆
                                      && i₆ < i₁₀
                                       ==> i₆ < 100000))
                               ==> (i₁₀ < 100000
                                 ==> a₈[i₁₀] == 10
                                  && 0 <= i₁₀ + 1
                                  && i₁₀ + 1 <= 100000
                                  && (forall i₆: int ::
                                        (  0 <= i₆
                                          && i₆ < i₁₀ + 1
                                           ==> i₆ < 100000))))))));

