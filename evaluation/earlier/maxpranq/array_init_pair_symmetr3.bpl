data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int, a: [int]int, b: [int]int, c: [int]int ::
      (0 < N
         ==> (  N < 100000
          && 0 < N
           ==> 1 <= 1
            && 1 <= N
            && (forall x₁₁: int, i₁₀: int ::
                  (  x₁₁ == i₁₀
                    && 1 <= i₁₀
                    && i₁₀ < 1
                     ==> (exists x₉: int, i₁₀: int ::
                            x₉ < 100000
                            && -100000 < x₉
                            && i₁₀ < N
                            && x₁₁ == i₁₀
                            && 1 <= i₁₀
                            && i₁₀ < 1
                            && a[x₁₁] == x₉ + N)))
            && (forall x₁₁: int ::
                    (exists i₁₀: int ::
                            x₁₁ == i₁₀
                            && 1 <= i₁₀
                            && i₁₀ < 1)
                    || a[x₁₁] == a[x₁₁])
            && (forall x₁₂: int, i₁₀: int ::
                  (  x₁₂ == i₁₀
                    && 1 <= i₁₀
                    && i₁₀ < 1
                     ==> (exists x₉: int, i₁₀: int ::
                            x₉ < 100000
                            && -100000 < x₉
                            && i₁₀ < N
                            && x₁₂ == i₁₀
                            && 1 <= i₁₀
                            && i₁₀ < 1
                            && b[x₁₂] == x₉)))
            && (forall x₁₂: int ::
                    (exists i₁₀: int ::
                            x₁₂ == i₁₀
                            && 1 <= i₁₀
                            && i₁₀ < 1)
                    || b[x₁₂] == b[x₁₂])
            && (forall i₁₀: int ::
                  (  1 <= i₁₀
                    && i₁₀ < 1
                     ==> i₁₀ < N))
            && (forall a₂₂: [int]int, b₂₃: [int]int, i₂₄: int ::
                  (  1 <= i₂₄
                    && i₂₄ <= N
                    && (forall x₁₁: int, i₁₀: int ::
                          (  x₁₁ == i₁₀
                            && 1 <= i₁₀
                            && i₁₀ < i₂₄
                             ==> (exists x₉: int, i₁₀: int ::
                                    x₉ < 100000
                                    && -100000 < x₉
                                    && i₁₀ < N
                                    && x₁₁ == i₁₀
                                    && 1 <= i₁₀
                                    && i₁₀ < i₂₄
                                    && a₂₂[x₁₁] == x₉ + N)))
                    && (forall x₁₁: int ::
                            (exists i₁₀: int ::
                                    x₁₁ == i₁₀
                                    && 1 <= i₁₀
                                    && i₁₀ < i₂₄)
                            || a₂₂[x₁₁] == a[x₁₁])
                    && (forall x₁₂: int, i₁₀: int ::
                          (  x₁₂ == i₁₀
                            && 1 <= i₁₀
                            && i₁₀ < i₂₄
                             ==> (exists x₉: int, i₁₀: int ::
                                    x₉ < 100000
                                    && -100000 < x₉
                                    && i₁₀ < N
                                    && x₁₂ == i₁₀
                                    && 1 <= i₁₀
                                    && i₁₀ < i₂₄
                                    && b₂₃[x₁₂] == x₉)))
                    && (forall x₁₂: int ::
                            (exists i₁₀: int ::
                                    x₁₂ == i₁₀
                                    && 1 <= i₁₀
                                    && i₁₀ < i₂₄)
                            || b₂₃[x₁₂] == b[x₁₂])
                    && (forall i₁₀: int ::
                          (  1 <= i₁₀
                            && i₁₀ < i₂₄
                             ==> i₁₀ < N))
                     ==> (forall x: int ::
                            (i₂₄ < N
                               ==> (  x < 100000
                                && -100000 < x
                                 ==> 1 <= i₂₄ + 1
                                  && i₂₄ + 1 <= N
                                  && (forall x₁₁: int, i₁₀: int ::
                                        (  x₁₁ == i₁₀
                                          && 1 <= i₁₀
                                          && i₁₀ < i₂₄ + 1
                                           ==> (exists x₉: int, i₁₀: int ::
                                                  x₉ < 100000
                                                  && -100000 < x₉
                                                  && i₁₀ < N
                                                  && x₁₁ == i₁₀
                                                  && 1 <= i₁₀
                                                  && i₁₀ < i₂₄ + 1
                                                  && a₂₂[i₂₄ := N + x][x₁₁] == x₉ + N)))
                                  && (forall x₁₁: int ::
                                          (exists i₁₀: int ::
                                                  x₁₁ == i₁₀
                                                  && 1 <= i₁₀
                                                  && i₁₀ < i₂₄ + 1)
                                          || a₂₂[i₂₄ := N + x][x₁₁] == a[x₁₁])
                                  && (forall x₁₂: int, i₁₀: int ::
                                        (  x₁₂ == i₁₀
                                          && 1 <= i₁₀
                                          && i₁₀ < i₂₄ + 1
                                           ==> (exists x₉: int, i₁₀: int ::
                                                  x₉ < 100000
                                                  && -100000 < x₉
                                                  && i₁₀ < N
                                                  && x₁₂ == i₁₀
                                                  && 1 <= i₁₀
                                                  && i₁₀ < i₂₄ + 1
                                                  && b₂₃[i₂₄ := x][x₁₂] == x₉)))
                                  && (forall x₁₂: int ::
                                          (exists i₁₀: int ::
                                                  x₁₂ == i₁₀
                                                  && 1 <= i₁₀
                                                  && i₁₀ < i₂₄ + 1)
                                          || b₂₃[i₂₄ := x][x₁₂] == b[x₁₂])
                                  && (forall i₁₀: int ::
                                        (  1 <= i₁₀
                                          && i₁₀ < i₂₄ + 1
                                           ==> i₁₀ < N)))))
                      &&   i₂₄ < N
                        ||   0 <= 0
                          && 0 <= N
                          && (forall x₁₇: int, i₁₆: int ::
                                (  x₁₇ == i₁₆
                                  && 0 <= i₁₆
                                  && i₁₆ < 0
                                   ==> (exists i₁₆: int ::
                                          i₁₆ < N
                                          && x₁₇ == i₁₆
                                          && 0 <= i₁₆
                                          && i₁₆ < 0
                                          && c[x₁₇] == a₂₂[i₁₆] + -b₂₃[i₁₆])))
                          && (forall x₁₇: int ::
                                  (exists i₁₆: int ::
                                          x₁₇ == i₁₆
                                          && 0 <= i₁₆
                                          && i₁₆ < 0)
                                  || c[x₁₇] == c[x₁₇])
                          && (forall i₁₆: int ::
                                (  0 <= i₁₆
                                  && i₁₆ < 0
                                   ==> i₁₆ < N))
                          && (forall c₂₅: [int]int, i₂₆: int ::
                                (  0 <= i₂₆
                                  && i₂₆ <= N
                                  && (forall x₁₇: int, i₁₆: int ::
                                        (  x₁₇ == i₁₆
                                          && 0 <= i₁₆
                                          && i₁₆ < i₂₆
                                           ==> (exists i₁₆: int ::
                                                  i₁₆ < N
                                                  && x₁₇ == i₁₆
                                                  && 0 <= i₁₆
                                                  && i₁₆ < i₂₆
                                                  && c₂₅[x₁₇] == a₂₂[i₁₆] + -b₂₃[i₁₆])))
                                  && (forall x₁₇: int ::
                                          (exists i₁₆: int ::
                                                  x₁₇ == i₁₆
                                                  && 0 <= i₁₆
                                                  && i₁₆ < i₂₆)
                                          || c₂₅[x₁₇] == c[x₁₇])
                                  && (forall i₁₆: int ::
                                        (  0 <= i₁₆
                                          && i₁₆ < i₂₆
                                           ==> i₁₆ < N))
                                   ==> (i₂₆ < N
                                       ==> 0 <= i₂₆ + 1
                                        && i₂₆ + 1 <= N
                                        && (forall x₁₇: int, i₁₆: int ::
                                              (  x₁₇ == i₁₆
                                                && 0 <= i₁₆
                                                && i₁₆ < i₂₆ + 1
                                                 ==> (exists i₁₆: int ::
                                                        i₁₆ < N
                                                        && x₁₇ == i₁₆
                                                        && 0 <= i₁₆
                                                        && i₁₆ < i₂₆ + 1
                                                        && c₂₅[i₂₆ := a₂₂[i₂₆] - b₂₃[i₂₆]][x₁₇] == a₂₂[i₁₆] + -b₂₃[i₁₆])))
                                        && (forall x₁₇: int ::
                                                (exists i₁₆: int ::
                                                        x₁₇ == i₁₆
                                                        && 0 <= i₁₆
                                                        && i₁₆ < i₂₆ + 1)
                                                || c₂₅[i₂₆ := a₂₂[i₂₆] - b₂₃[i₂₆]][x₁₇] == c[x₁₇])
                                        && (forall i₁₆: int ::
                                              (  0 <= i₁₆
                                                && i₁₆ < i₂₆ + 1
                                                 ==> i₁₆ < N)))
                                    &&   i₂₆ < N
                                      ||   1 <= 1
                                        && 1 <= N
                                        && (forall i₂₀: int ::
                                              (  1 <= i₂₀
                                                && i₂₀ < 1
                                                 ==> i₂₀ < N))
                                        && (forall i₂₇: int ::
                                              (  1 <= i₂₇
                                                && i₂₇ <= N
                                                && (forall i₂₀: int ::
                                                      (  1 <= i₂₀
                                                        && i₂₀ < i₂₇
                                                         ==> i₂₀ < N))
                                                 ==> (i₂₇ < N
                                                   ==> c₂₅[i₂₇] == N
                                                    && 1 <= i₂₇ + 1
                                                    && i₂₇ + 1 <= N
                                                    && (forall i₂₀: int ::
                                                          (  1 <= i₂₀
                                                            && i₂₀ < i₂₇ + 1
                                                             ==> i₂₀ < N))))))))))));

