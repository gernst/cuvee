data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall A₄₅: [int][int]int, B₄₆: [int][int]int, i₄₇: int, A₇₈: [int][int]int, B₇₉: [int][int]int, j₈₀: int, i₁₃: int ::
      (  0 <= i₄₇
        && (forall i₁₇₄: int ::
              (  0 <= i₁₇₄
                && i₁₇₄ < i₄₇
                 ==> (exists A₉: [int][int]int, B₁₀: [int][int]int, j₁₁: int ::
                        0 <= j₁₁
                        && (forall j₈: int ::
                              (  0 <= j₈
                                && j₈ < j₁₁
                                 ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                                        j₈ < 1500
                                        && A₉[i₁₇₄][j₈] == nondet_uint₁₆
                                        && B₁₀[i₁₇₄][j₈] == nondet_uint₂₇)))
                        && (forall j₈: int ::
                                  0 <= j₈
                                  && j₈ < j₁₁
                                ||   A₉[i₁₇₄][j₈] == A₄₅[i₁₇₄][j₈]
                                  && B₁₀[i₁₇₄][j₈] == B₄₆[i₁₇₄][j₈])
                        && (j₁₁ < 1500
                           ==> false)
                        && i₁₇₄ < 1000)))
        && i₄₇ < 1000
        && 0 <= j₈₀
        && (forall j₈: int ::
              (  0 <= j₈
                && j₈ < j₈₀
                 ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                        j₈ < 1500
                        && A₇₈[i₄₇][j₈] == nondet_uint₁₆
                        && B₇₉[i₄₇][j₈] == nondet_uint₂₇)))
        && (forall j₈: int ::
                  0 <= j₈
                  && j₈ < j₈₀
                ||   A₇₈[i₄₇][j₈] == A₄₅[i₄₇][j₈]
                  && B₇₉[i₄₇][j₈] == B₄₆[i₄₇][j₈])
        && 0 <= i₁₃
        && i₁₃ < i₄₇ + 1
         ==> j₈₀ < 1500
          || (exists A₉: [int][int]int, B₁₀: [int][int]int, j₁₁: int ::
                  0 <= j₁₁
                  && (forall j₈: int ::
                        (  0 <= j₈
                          && j₈ < j₁₁
                           ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                                  j₈ < 1500
                                  && A₉[i₁₃][j₈] == nondet_uint₁₆
                                  && B₁₀[i₁₃][j₈] == nondet_uint₂₇)))
                  && (forall j₈: int ::
                            0 <= j₈
                            && j₈ < j₁₁
                          ||   A₉[i₁₃][j₈] == A₇₈[i₁₃][j₈]
                            && B₁₀[i₁₃][j₈] == B₇₉[i₁₃][j₈])
                  && (j₁₁ < 1500
                     ==> false)
                  && i₁₃ < 1000)));

goal {:named "invariant forward"} (forall A₄₅: [int][int]int, B₄₆: [int][int]int, i₄₇: int, A₄₉: [int][int]int, B₅₀: [int][int]int, i₅₁: int, A₆₈: [int][int]int, B₆₉: [int][int]int, j₇₀: int, i₂₅: int ::
      (  0 <= i₄₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₄₇
                 ==> (exists A₉: [int][int]int, B₁₀: [int][int]int, j₁₁: int ::
                        0 <= j₁₁
                        && (forall j₈: int ::
                              (  0 <= j₈
                                && j₈ < j₁₁
                                 ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                                        j₈ < 1500
                                        && A₉[i₁₃][j₈] == nondet_uint₁₆
                                        && B₁₀[i₁₃][j₈] == nondet_uint₂₇)))
                        && (forall j₈: int ::
                                  0 <= j₈
                                  && j₈ < j₁₁
                                ||   A₉[i₁₃][j₈] == A₄₅[i₁₃][j₈]
                                  && B₁₀[i₁₃][j₈] == B₄₆[i₁₃][j₈])
                        && (j₁₁ < 1500
                           ==> false)
                        && i₁₃ < 1000)))
        && 0 <= i₅₁
        && (forall i₃₀₇: int ::
              (  0 <= i₃₀₇
                && i₃₀₇ < i₅₁
                 ==> (exists A₂₁: [int][int]int, B₂₂: [int][int]int, j₂₃: int ::
                        0 <= j₂₃
                        && (forall j₂₀: int ::
                              (  0 <= j₂₀
                                && j₂₀ < j₂₃
                                 ==> (exists nondet_uint₃₁₈: int, nondet_uint₄₁₉: int ::
                                        j₂₀ < 1500
                                        && A₂₁[i₃₀₇][j₂₀] == nondet_uint₃₁₈
                                        && B₂₂[i₃₀₇][j₂₀] == nondet_uint₄₁₉)))
                        && (forall j₂₀: int ::
                                  0 <= j₂₀
                                  && j₂₀ < j₂₃
                                ||   A₂₁[i₃₀₇][j₂₀] == A₄₉[i₃₀₇][j₂₀]
                                  && B₂₂[i₃₀₇][j₂₀] == B₅₀[i₃₀₇][j₂₀])
                        && (j₂₃ < 1500
                           ==> false)
                        && i₃₀₇ < 1000)))
        && i₅₁ < 1000
        && 0 <= j₇₀
        && (forall j₂₀: int ::
              (  0 <= j₂₀
                && j₂₀ < j₇₀
                 ==> (exists nondet_uint₃₁₈: int, nondet_uint₄₁₉: int ::
                        j₂₀ < 1500
                        && A₆₈[i₅₁][j₂₀] == nondet_uint₃₁₈
                        && B₆₉[i₅₁][j₂₀] == nondet_uint₄₁₉)))
        && (forall j₂₀: int ::
                  0 <= j₂₀
                  && j₂₀ < j₇₀
                ||   A₆₈[i₅₁][j₂₀] == A₄₉[i₅₁][j₂₀]
                  && B₆₉[i₅₁][j₂₀] == B₅₀[i₅₁][j₂₀])
        && 0 <= i₂₅
        && i₂₅ < i₅₁ + 1
         ==> j₇₀ < 1500
          || i₄₇ < 1000
          || (exists A₂₁: [int][int]int, B₂₂: [int][int]int, j₂₃: int ::
                  0 <= j₂₃
                  && (forall j₂₀: int ::
                        (  0 <= j₂₀
                          && j₂₀ < j₂₃
                           ==> (exists nondet_uint₃₁₈: int, nondet_uint₄₁₉: int ::
                                  j₂₀ < 1500
                                  && A₂₁[i₂₅][j₂₀] == nondet_uint₃₁₈
                                  && B₂₂[i₂₅][j₂₀] == nondet_uint₄₁₉)))
                  && (forall j₂₀: int ::
                            0 <= j₂₀
                            && j₂₀ < j₂₃
                          ||   A₂₁[i₂₅][j₂₀] == A₆₈[i₂₅][j₂₀]
                            && B₂₂[i₂₅][j₂₀] == B₆₉[i₂₅][j₂₀])
                  && (j₂₃ < 1500
                     ==> false)
                  && i₂₅ < 1000)));

goal {:named "invariant forward"} (forall A₄₅: [int][int]int, B₄₆: [int][int]int, i₄₇: int, A₄₉: [int][int]int, B₅₀: [int][int]int, i₅₁: int, C₅₃: [int][int]int, i₅₄: int, C₆₁: [int][int]int, j₆₂: int, i₃₄: int ::
      (  0 <= i₄₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₄₇
                 ==> (exists A₉: [int][int]int, B₁₀: [int][int]int, j₁₁: int ::
                        0 <= j₁₁
                        && (forall j₈: int ::
                              (  0 <= j₈
                                && j₈ < j₁₁
                                 ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                                        j₈ < 1500
                                        && A₉[i₁₃][j₈] == nondet_uint₁₆
                                        && B₁₀[i₁₃][j₈] == nondet_uint₂₇)))
                        && (forall j₈: int ::
                                  0 <= j₈
                                  && j₈ < j₁₁
                                ||   A₉[i₁₃][j₈] == A₄₅[i₁₃][j₈]
                                  && B₁₀[i₁₃][j₈] == B₄₆[i₁₃][j₈])
                        && (j₁₁ < 1500
                           ==> false)
                        && i₁₃ < 1000)))
        && 0 <= i₅₁
        && (forall i₂₅: int ::
              (  0 <= i₂₅
                && i₂₅ < i₅₁
                 ==> (exists A₂₁: [int][int]int, B₂₂: [int][int]int, j₂₃: int ::
                        0 <= j₂₃
                        && (forall j₂₀: int ::
                              (  0 <= j₂₀
                                && j₂₀ < j₂₃
                                 ==> (exists nondet_uint₃₁₈: int, nondet_uint₄₁₉: int ::
                                        j₂₀ < 1500
                                        && A₂₁[i₂₅][j₂₀] == nondet_uint₃₁₈
                                        && B₂₂[i₂₅][j₂₀] == nondet_uint₄₁₉)))
                        && (forall j₂₀: int ::
                                  0 <= j₂₀
                                  && j₂₀ < j₂₃
                                ||   A₂₁[i₂₅][j₂₀] == A₄₉[i₂₅][j₂₀]
                                  && B₂₂[i₂₅][j₂₀] == B₅₀[i₂₅][j₂₀])
                        && (j₂₃ < 1500
                           ==> false)
                        && i₂₅ < 1000)))
        && 0 <= i₅₄
        && (forall i₄₄₁: int ::
              (  0 <= i₄₄₁
                && i₄₄₁ < i₅₄
                 ==> (exists C₃₁: [int][int]int, j₃₂: int ::
                        0 <= j₃₂
                        && (forall j₃₀: int ::
                              (  0 <= j₃₀
                                && j₃₀ < j₃₂
                                 ==> j₃₀ < 1500
                                  && C₃₁[i₄₄₁][j₃₀] == A₄₉[i₄₄₁][j₃₀] + -B₅₀[i₄₄₁][j₃₀]))
                        && (forall j₃₀: int ::
                                  0 <= j₃₀
                                  && j₃₀ < j₃₂
                                || C₃₁[i₄₄₁][j₃₀] == C₅₃[i₄₄₁][j₃₀])
                        && (j₃₂ < 1500
                           ==> false)
                        && i₄₄₁ < 1000)))
        && i₅₄ < 1000
        && 0 <= j₆₂
        && (forall j₃₀: int ::
              (  0 <= j₃₀
                && j₃₀ < j₆₂
                 ==> j₃₀ < 1500
                  && C₆₁[i₅₄][j₃₀] == -B₅₀[i₅₄][j₃₀] + A₄₉[i₅₄][j₃₀]))
        && (forall j₃₀: int ::
                  0 <= j₃₀
                  && j₃₀ < j₆₂
                || C₆₁[i₅₄][j₃₀] == C₅₃[i₅₄][j₃₀])
        && 0 <= i₃₄
        && i₃₄ < i₅₄ + 1
         ==> j₆₂ < 1500
          || i₅₁ < 1000
          || i₄₇ < 1000
          || (exists C₃₁: [int][int]int, j₃₂: int ::
                  0 <= j₃₂
                  && (forall j₃₀: int ::
                        (  0 <= j₃₀
                          && j₃₀ < j₃₂
                           ==> j₃₀ < 1500
                            && C₃₁[i₃₄][j₃₀] == A₄₉[i₃₄][j₃₀] + -B₅₀[i₃₄][j₃₀]))
                  && (forall j₃₀: int ::
                            0 <= j₃₀
                            && j₃₀ < j₃₂
                          || C₃₁[i₃₄][j₃₀] == C₆₁[i₃₄][j₃₀])
                  && (j₃₂ < 1500
                     ==> false)
                  && i₃₄ < 1000)));

goal {:named "assert"} (forall A₄₅: [int][int]int, B₄₆: [int][int]int, i₄₇: int, A₄₉: [int][int]int, B₅₀: [int][int]int, i₅₁: int, C₅₃: [int][int]int, i₅₄: int, i₅₆: int, j₅₇: int ::
      (  0 <= i₄₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₄₇
                 ==> (exists A₉: [int][int]int, B₁₀: [int][int]int, j₁₁: int ::
                        0 <= j₁₁
                        && (forall j₈: int ::
                              (  0 <= j₈
                                && j₈ < j₁₁
                                 ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                                        j₈ < 1500
                                        && A₉[i₁₃][j₈] == nondet_uint₁₆
                                        && B₁₀[i₁₃][j₈] == nondet_uint₂₇)))
                        && (forall j₈: int ::
                                  0 <= j₈
                                  && j₈ < j₁₁
                                ||   A₉[i₁₃][j₈] == A₄₅[i₁₃][j₈]
                                  && B₁₀[i₁₃][j₈] == B₄₆[i₁₃][j₈])
                        && (j₁₁ < 1500
                           ==> false)
                        && i₁₃ < 1000)))
        && 0 <= i₅₁
        && (forall i₂₅: int ::
              (  0 <= i₂₅
                && i₂₅ < i₅₁
                 ==> (exists A₂₁: [int][int]int, B₂₂: [int][int]int, j₂₃: int ::
                        0 <= j₂₃
                        && (forall j₂₀: int ::
                              (  0 <= j₂₀
                                && j₂₀ < j₂₃
                                 ==> (exists nondet_uint₃₁₈: int, nondet_uint₄₁₉: int ::
                                        j₂₀ < 1500
                                        && A₂₁[i₂₅][j₂₀] == nondet_uint₃₁₈
                                        && B₂₂[i₂₅][j₂₀] == nondet_uint₄₁₉)))
                        && (forall j₂₀: int ::
                                  0 <= j₂₀
                                  && j₂₀ < j₂₃
                                ||   A₂₁[i₂₅][j₂₀] == A₄₉[i₂₅][j₂₀]
                                  && B₂₂[i₂₅][j₂₀] == B₅₀[i₂₅][j₂₀])
                        && (j₂₃ < 1500
                           ==> false)
                        && i₂₅ < 1000)))
        && 0 <= i₅₄
        && (forall i₃₄: int ::
              (  0 <= i₃₄
                && i₃₄ < i₅₄
                 ==> (exists C₃₁: [int][int]int, j₃₂: int ::
                        0 <= j₃₂
                        && (forall j₃₀: int ::
                              (  0 <= j₃₀
                                && j₃₀ < j₃₂
                                 ==> j₃₀ < 1500
                                  && C₃₁[i₃₄][j₃₀] == A₄₉[i₃₄][j₃₀] + -B₅₀[i₃₄][j₃₀]))
                        && (forall j₃₀: int ::
                                  0 <= j₃₀
                                  && j₃₀ < j₃₂
                                || C₃₁[i₃₄][j₃₀] == C₅₃[i₃₄][j₃₀])
                        && (j₃₂ < 1500
                           ==> false)
                        && i₃₄ < 1000)))
        && 0 <= i₅₆
        && (forall i₄₁: int ::
              (  0 <= i₄₁
                && i₄₁ < i₅₆
                 ==> (exists j₃₉: int ::
                        0 <= j₃₉
                        && (forall j₃₈: int ::
                              (  0 <= j₃₈
                                && j₃₈ < j₃₉
                                 ==> j₃₈ < 1500))
                        && (j₃₉ < 1500
                           ==> false)
                        && i₄₁ < 1000)))
        && i₅₆ < 1000
        && 0 <= j₅₇
        && (forall j₃₈: int ::
              (  0 <= j₃₈
                && j₃₈ < j₅₇
                 ==> j₃₈ < 1500))
        && j₅₇ < 1500
         ==> i₅₄ < 1000
          || i₅₁ < 1000
          || i₄₇ < 1000
          || C₅₃[i₅₆][j₅₇] == A₄₉[i₅₆][j₅₇] - B₅₀[i₅₆][j₅₇]));

