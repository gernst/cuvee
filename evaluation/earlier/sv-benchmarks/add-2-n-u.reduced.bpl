data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall A₃₃: [int][int]int, B₃₄: [int][int]int, i₃₅: int, A₅₂: [int][int]int, B₅₃: [int][int]int, j₅₄: int, i₁₃: int ::
      (  0 <= i₃₅
        && (forall i₁₄₈: int ::
              (  0 <= i₁₄₈
                && i₁₄₈ < i₃₅
                 ==> (exists A₉: [int][int]int, B₁₀: [int][int]int, j₁₁: int ::
                        0 <= j₁₁
                        && (forall j₈: int ::
                              (  0 <= j₈
                                && j₈ < j₁₁
                                 ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                                        j₈ < 1500
                                        && A₉[i₁₄₈][j₈] == nondet_uint₁₆
                                        && B₁₀[i₁₄₈][j₈] == nondet_uint₂₇)))
                        && (forall j₈: int ::
                                  0 <= j₈
                                  && j₈ < j₁₁
                                ||   A₉[i₁₄₈][j₈] == A₃₃[i₁₄₈][j₈]
                                  && B₁₀[i₁₄₈][j₈] == B₃₄[i₁₄₈][j₈])
                        && (j₁₁ < 1500
                           ==> false)
                        && i₁₄₈ < 1000)))
        && i₃₅ < 1000
        && 0 <= j₅₄
        && (forall j₈: int ::
              (  0 <= j₈
                && j₈ < j₅₄
                 ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                        j₈ < 1500
                        && A₅₂[i₃₅][j₈] == nondet_uint₁₆
                        && B₅₃[i₃₅][j₈] == nondet_uint₂₇)))
        && (forall j₈: int ::
                  0 <= j₈
                  && j₈ < j₅₄
                ||   A₅₂[i₃₅][j₈] == A₃₃[i₃₅][j₈]
                  && B₅₃[i₃₅][j₈] == B₃₄[i₃₅][j₈])
        && 0 <= i₁₃
        && i₁₃ < i₃₅ + 1
         ==> j₅₄ < 1500
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
                          ||   A₉[i₁₃][j₈] == A₅₂[i₁₃][j₈]
                            && B₁₀[i₁₃][j₈] == B₅₃[i₁₃][j₈])
                  && (j₁₁ < 1500
                     ==> false)
                  && i₁₃ < 1000)));

goal {:named "invariant forward"} (forall A₃₃: [int][int]int, B₃₄: [int][int]int, i₃₅: int, C₃₇: [int][int]int, i₃₈: int, C₄₅: [int][int]int, j₄₆: int, i₂₂: int ::
      (  0 <= i₃₅
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₃₅
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
                                ||   A₉[i₁₃][j₈] == A₃₃[i₁₃][j₈]
                                  && B₁₀[i₁₃][j₈] == B₃₄[i₁₃][j₈])
                        && (j₁₁ < 1500
                           ==> false)
                        && i₁₃ < 1000)))
        && 0 <= i₃₈
        && (forall i₂₄₀: int ::
              (  0 <= i₂₄₀
                && i₂₄₀ < i₃₈
                 ==> (exists C₁₉: [int][int]int, j₂₀: int ::
                        0 <= j₂₀
                        && (forall j₁₈: int ::
                              (  0 <= j₁₈
                                && j₁₈ < j₂₀
                                 ==> j₁₈ < 1500
                                  && C₁₉[i₂₄₀][j₁₈] == B₃₄[i₂₄₀][j₁₈] + A₃₃[i₂₄₀][j₁₈]))
                        && (forall j₁₈: int ::
                                  0 <= j₁₈
                                  && j₁₈ < j₂₀
                                || C₁₉[i₂₄₀][j₁₈] == C₃₇[i₂₄₀][j₁₈])
                        && (j₂₀ < 1500
                           ==> false)
                        && i₂₄₀ < 1000)))
        && i₃₈ < 1000
        && 0 <= j₄₆
        && (forall j₁₈: int ::
              (  0 <= j₁₈
                && j₁₈ < j₄₆
                 ==> j₁₈ < 1500
                  && C₄₅[i₃₈][j₁₈] == B₃₄[i₃₈][j₁₈] + A₃₃[i₃₈][j₁₈]))
        && (forall j₁₈: int ::
                  0 <= j₁₈
                  && j₁₈ < j₄₆
                || C₄₅[i₃₈][j₁₈] == C₃₇[i₃₈][j₁₈])
        && 0 <= i₂₂
        && i₂₂ < i₃₈ + 1
         ==> j₄₆ < 1500
          || i₃₅ < 1000
          || (exists C₁₉: [int][int]int, j₂₀: int ::
                  0 <= j₂₀
                  && (forall j₁₈: int ::
                        (  0 <= j₁₈
                          && j₁₈ < j₂₀
                           ==> j₁₈ < 1500
                            && C₁₉[i₂₂][j₁₈] == B₃₄[i₂₂][j₁₈] + A₃₃[i₂₂][j₁₈]))
                  && (forall j₁₈: int ::
                            0 <= j₁₈
                            && j₁₈ < j₂₀
                          || C₁₉[i₂₂][j₁₈] == C₄₅[i₂₂][j₁₈])
                  && (j₂₀ < 1500
                     ==> false)
                  && i₂₂ < 1000)));

goal {:named "assert"} (forall A₃₃: [int][int]int, B₃₄: [int][int]int, i₃₅: int, C₃₇: [int][int]int, i₃₈: int, i₄₀: int, j₄₁: int ::
      (  0 <= i₃₅
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₃₅
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
                                ||   A₉[i₁₃][j₈] == A₃₃[i₁₃][j₈]
                                  && B₁₀[i₁₃][j₈] == B₃₄[i₁₃][j₈])
                        && (j₁₁ < 1500
                           ==> false)
                        && i₁₃ < 1000)))
        && 0 <= i₃₈
        && (forall i₂₂: int ::
              (  0 <= i₂₂
                && i₂₂ < i₃₈
                 ==> (exists C₁₉: [int][int]int, j₂₀: int ::
                        0 <= j₂₀
                        && (forall j₁₈: int ::
                              (  0 <= j₁₈
                                && j₁₈ < j₂₀
                                 ==> j₁₈ < 1500
                                  && C₁₉[i₂₂][j₁₈] == B₃₄[i₂₂][j₁₈] + A₃₃[i₂₂][j₁₈]))
                        && (forall j₁₈: int ::
                                  0 <= j₁₈
                                  && j₁₈ < j₂₀
                                || C₁₉[i₂₂][j₁₈] == C₃₇[i₂₂][j₁₈])
                        && (j₂₀ < 1500
                           ==> false)
                        && i₂₂ < 1000)))
        && 0 <= i₄₀
        && (forall i₂₉: int ::
              (  0 <= i₂₉
                && i₂₉ < i₄₀
                 ==> (exists j₂₇: int ::
                        0 <= j₂₇
                        && (forall j₂₆: int ::
                              (  0 <= j₂₆
                                && j₂₆ < j₂₇
                                 ==> j₂₆ < 1500))
                        && (j₂₇ < 1500
                           ==> false)
                        && i₂₉ < 1000)))
        && i₄₀ < 1000
        && 0 <= j₄₁
        && (forall j₂₆: int ::
              (  0 <= j₂₆
                && j₂₆ < j₄₁
                 ==> j₂₆ < 1500))
        && j₄₁ < 1500
         ==> i₃₈ < 1000
          || i₃₅ < 1000
          || C₃₇[i₄₀][j₄₁] == A₃₃[i₄₀][j₄₁] + B₃₄[i₄₀][j₄₁]));

