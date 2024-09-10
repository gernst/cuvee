data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall i₅₅: int, A₉₀: [int][int][int]int, B₉₁: [int][int][int]int, j₉₂: int, A₉₈: [int][int][int]int, B₉₉: [int][int][int]int, k₁₀₀: int, j₁₄: int ::
      (  0 <= i₅₅
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₅₅
                 ==> (exists A₁₆: [int][int][int]int, B₁₇: [int][int][int]int, j₁₈: int ::
                        0 <= j₁₈
                        && (forall j₂₁₇: int ::
                              (  0 <= j₂₁₇
                                && j₂₁₇ < j₁₈
                                 ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                                        0 <= k₁₂
                                        && (forall k₉: int ::
                                              (  0 <= k₉
                                                && k₉ < k₁₂
                                                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                                        0 <= nondet_uint₂₈
                                                        && nondet_uint₂₈ < 4294967296
                                                        && 0 <= nondet_uint₁₇
                                                        && nondet_uint₁₇ < 4294967296
                                                        && k₉ < 1800
                                                        && A₁₀[i₂₀][j₂₁₇][k₉] == nondet_uint₁₇
                                                        && B₁₁[i₂₀][j₂₁₇][k₉] == nondet_uint₂₈)))
                                        && (forall k₉: int ::
                                                  0 <= k₉
                                                  && k₉ < k₁₂
                                                ||   A₁₀[i₂₀][j₂₁₇][k₉] == A₁₆[i₂₀][j₂₁₇][k₉]
                                                  && B₁₁[i₂₀][j₂₁₇][k₉] == B₁₇[i₂₀][j₂₁₇][k₉])
                                        && (k₁₂ < 1800
                                           ==> false)
                                        && j₂₁₇ < 1500)))
                        && (j₁₈ < 1500
                           ==> false)
                        && i₂₀ < 1000)))
        && i₅₅ < 1000
        && 0 <= j₉₂
        && (forall j₂₁₈: int ::
              (  0 <= j₂₁₈
                && j₂₁₈ < j₉₂
                 ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                        0 <= k₁₂
                        && (forall k₉: int ::
                              (  0 <= k₉
                                && k₉ < k₁₂
                                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                        0 <= nondet_uint₂₈
                                        && nondet_uint₂₈ < 4294967296
                                        && 0 <= nondet_uint₁₇
                                        && nondet_uint₁₇ < 4294967296
                                        && k₉ < 1800
                                        && A₁₀[i₅₅][j₂₁₈][k₉] == nondet_uint₁₇
                                        && B₁₁[i₅₅][j₂₁₈][k₉] == nondet_uint₂₈)))
                        && (forall k₉: int ::
                                  0 <= k₉
                                  && k₉ < k₁₂
                                ||   A₁₀[i₅₅][j₂₁₈][k₉] == A₉₀[i₅₅][j₂₁₈][k₉]
                                  && B₁₁[i₅₅][j₂₁₈][k₉] == B₉₁[i₅₅][j₂₁₈][k₉])
                        && (k₁₂ < 1800
                           ==> false)
                        && j₂₁₈ < 1500)))
        && j₉₂ < 1500
        && 0 <= k₁₀₀
        && (forall k₉: int ::
              (  0 <= k₉
                && k₉ < k₁₀₀
                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                        0 <= nondet_uint₂₈
                        && nondet_uint₂₈ < 4294967296
                        && 0 <= nondet_uint₁₇
                        && nondet_uint₁₇ < 4294967296
                        && k₉ < 1800
                        && A₉₈[i₅₅][j₉₂][k₉] == nondet_uint₁₇
                        && B₉₉[i₅₅][j₉₂][k₉] == nondet_uint₂₈)))
        && (forall k₉: int ::
                  0 <= k₉
                  && k₉ < k₁₀₀
                ||   A₉₈[i₅₅][j₉₂][k₉] == A₉₀[i₅₅][j₉₂][k₉]
                  && B₉₉[i₅₅][j₉₂][k₉] == B₉₁[i₅₅][j₉₂][k₉])
        && 0 <= j₁₄
        && j₁₄ < j₉₂ + 1
         ==> k₁₀₀ < 1800
          || (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                  0 <= k₁₂
                  && (forall k₉: int ::
                        (  0 <= k₉
                          && k₉ < k₁₂
                           ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                  0 <= nondet_uint₂₈
                                  && nondet_uint₂₈ < 4294967296
                                  && 0 <= nondet_uint₁₇
                                  && nondet_uint₁₇ < 4294967296
                                  && k₉ < 1800
                                  && A₁₀[i₅₅][j₁₄][k₉] == nondet_uint₁₇
                                  && B₁₁[i₅₅][j₁₄][k₉] == nondet_uint₂₈)))
                  && (forall k₉: int ::
                            0 <= k₉
                            && k₉ < k₁₂
                          ||   A₁₀[i₅₅][j₁₄][k₉] == A₉₈[i₅₅][j₁₄][k₉]
                            && B₁₁[i₅₅][j₁₄][k₉] == B₉₉[i₅₅][j₁₄][k₉])
                  && (k₁₂ < 1800
                     ==> false)
                  && j₁₄ < 1500)));

goal {:named "invariant forward"} (forall i₅₅: int, A₉₀: [int][int][int]int, B₉₁: [int][int][int]int, j₉₂: int, i₂₀: int ::
      (  0 <= i₅₅
        && (forall i₂₂₈: int ::
              (  0 <= i₂₂₈
                && i₂₂₈ < i₅₅
                 ==> (exists A₁₆: [int][int][int]int, B₁₇: [int][int][int]int, j₁₈: int ::
                        0 <= j₁₈
                        && (forall j₁₄: int ::
                              (  0 <= j₁₄
                                && j₁₄ < j₁₈
                                 ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                                        0 <= k₁₂
                                        && (forall k₉: int ::
                                              (  0 <= k₉
                                                && k₉ < k₁₂
                                                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                                        0 <= nondet_uint₂₈
                                                        && nondet_uint₂₈ < 4294967296
                                                        && 0 <= nondet_uint₁₇
                                                        && nondet_uint₁₇ < 4294967296
                                                        && k₉ < 1800
                                                        && A₁₀[i₂₂₈][j₁₄][k₉] == nondet_uint₁₇
                                                        && B₁₁[i₂₂₈][j₁₄][k₉] == nondet_uint₂₈)))
                                        && (forall k₉: int ::
                                                  0 <= k₉
                                                  && k₉ < k₁₂
                                                ||   A₁₀[i₂₂₈][j₁₄][k₉] == A₁₆[i₂₂₈][j₁₄][k₉]
                                                  && B₁₁[i₂₂₈][j₁₄][k₉] == B₁₇[i₂₂₈][j₁₄][k₉])
                                        && (k₁₂ < 1800
                                           ==> false)
                                        && j₁₄ < 1500)))
                        && (j₁₈ < 1500
                           ==> false)
                        && i₂₂₈ < 1000)))
        && i₅₅ < 1000
        && 0 <= j₉₂
        && (forall j₁₄: int ::
              (  0 <= j₁₄
                && j₁₄ < j₉₂
                 ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                        0 <= k₁₂
                        && (forall k₉: int ::
                              (  0 <= k₉
                                && k₉ < k₁₂
                                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                        0 <= nondet_uint₂₈
                                        && nondet_uint₂₈ < 4294967296
                                        && 0 <= nondet_uint₁₇
                                        && nondet_uint₁₇ < 4294967296
                                        && k₉ < 1800
                                        && A₁₀[i₅₅][j₁₄][k₉] == nondet_uint₁₇
                                        && B₁₁[i₅₅][j₁₄][k₉] == nondet_uint₂₈)))
                        && (forall k₉: int ::
                                  0 <= k₉
                                  && k₉ < k₁₂
                                ||   A₁₀[i₅₅][j₁₄][k₉] == A₉₀[i₅₅][j₁₄][k₉]
                                  && B₁₁[i₅₅][j₁₄][k₉] == B₉₁[i₅₅][j₁₄][k₉])
                        && (k₁₂ < 1800
                           ==> false)
                        && j₁₄ < 1500)))
        && 0 <= i₂₀
        && i₂₀ < i₅₅ + 1
         ==> j₉₂ < 1500
          || (exists A₁₆: [int][int][int]int, B₁₇: [int][int][int]int, j₁₈: int ::
                  0 <= j₁₈
                  && (forall j₁₄: int ::
                        (  0 <= j₁₄
                          && j₁₄ < j₁₈
                           ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                                  0 <= k₁₂
                                  && (forall k₉: int ::
                                        (  0 <= k₉
                                          && k₉ < k₁₂
                                           ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                                  0 <= nondet_uint₂₈
                                                  && nondet_uint₂₈ < 4294967296
                                                  && 0 <= nondet_uint₁₇
                                                  && nondet_uint₁₇ < 4294967296
                                                  && k₉ < 1800
                                                  && A₁₀[i₂₀][j₁₄][k₉] == nondet_uint₁₇
                                                  && B₁₁[i₂₀][j₁₄][k₉] == nondet_uint₂₈)))
                                  && (forall k₉: int ::
                                            0 <= k₉
                                            && k₉ < k₁₂
                                          ||   A₁₀[i₂₀][j₁₄][k₉] == A₁₆[i₂₀][j₁₄][k₉]
                                            && B₁₁[i₂₀][j₁₄][k₉] == B₁₇[i₂₀][j₁₄][k₉])
                                  && (k₁₂ < 1800
                                     ==> false)
                                  && j₁₄ < 1500)))
                  && (j₁₈ < 1500
                     ==> false)
                  && i₂₀ < 1000)));

goal {:named "invariant forward"} (forall i₅₅: int, B₅₆: [int][int][int]int, A₅₈: [int][int][int]int, i₆₂: int, C₇₆: [int][int][int]int, j₇₇: int, C₈₂: [int][int][int]int, k₈₃: int, j₃₁: int ::
      (  0 <= i₅₅
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₅₅
                 ==> (exists A₁₆: [int][int][int]int, B₁₇: [int][int][int]int, j₁₈: int ::
                        0 <= j₁₈
                        && (forall j₁₄: int ::
                              (  0 <= j₁₄
                                && j₁₄ < j₁₈
                                 ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                                        0 <= k₁₂
                                        && (forall k₉: int ::
                                              (  0 <= k₉
                                                && k₉ < k₁₂
                                                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                                        0 <= nondet_uint₂₈
                                                        && nondet_uint₂₈ < 4294967296
                                                        && 0 <= nondet_uint₁₇
                                                        && nondet_uint₁₇ < 4294967296
                                                        && k₉ < 1800
                                                        && A₁₀[i₂₀][j₁₄][k₉] == nondet_uint₁₇
                                                        && B₁₁[i₂₀][j₁₄][k₉] == nondet_uint₂₈)))
                                        && (forall k₉: int ::
                                                  0 <= k₉
                                                  && k₉ < k₁₂
                                                ||   A₁₀[i₂₀][j₁₄][k₉] == A₁₆[i₂₀][j₁₄][k₉]
                                                  && B₁₁[i₂₀][j₁₄][k₉] == B₁₇[i₂₀][j₁₄][k₉])
                                        && (k₁₂ < 1800
                                           ==> false)
                                        && j₁₄ < 1500)))
                        && (j₁₈ < 1500
                           ==> false)
                        && i₂₀ < 1000)))
        && 0 <= i₆₂
        && (forall i₃₇: int ::
              (  0 <= i₃₇
                && i₃₇ < i₆₂
                 ==> (exists C₃₃: [int][int][int]int, j₃₄: int ::
                        0 <= j₃₄
                        && (forall j₃₃₉: int ::
                              (  0 <= j₃₃₉
                                && j₃₃₉ < j₃₄
                                 ==> (exists C₂₈: [int][int][int]int, k₂₉: int ::
                                        0 <= k₂₉
                                        && (forall k₂₇: int ::
                                              (  0 <= k₂₇
                                                && k₂₇ < k₂₉
                                                 ==> k₂₇ < 1800
                                                  && C₂₈[i₃₇][j₃₃₉][k₂₇] == B₅₆[i₃₇][j₃₃₉][k₂₇] + A₅₈[i₃₇][j₃₃₉][k₂₇]))
                                        && (forall k₂₇: int ::
                                                  0 <= k₂₇
                                                  && k₂₇ < k₂₉
                                                || C₂₈[i₃₇][j₃₃₉][k₂₇] == C₃₃[i₃₇][j₃₃₉][k₂₇])
                                        && (k₂₉ < 1800
                                           ==> false)
                                        && j₃₃₉ < 1500)))
                        && (j₃₄ < 1500
                           ==> false)
                        && i₃₇ < 1000)))
        && i₆₂ < 1000
        && 0 <= j₇₇
        && (forall j₃₄₀: int ::
              (  0 <= j₃₄₀
                && j₃₄₀ < j₇₇
                 ==> (exists C₂₈: [int][int][int]int, k₂₉: int ::
                        0 <= k₂₉
                        && (forall k₂₇: int ::
                              (  0 <= k₂₇
                                && k₂₇ < k₂₉
                                 ==> k₂₇ < 1800
                                  && C₂₈[i₆₂][j₃₄₀][k₂₇] == B₅₆[i₆₂][j₃₄₀][k₂₇] + A₅₈[i₆₂][j₃₄₀][k₂₇]))
                        && (forall k₂₇: int ::
                                  0 <= k₂₇
                                  && k₂₇ < k₂₉
                                || C₂₈[i₆₂][j₃₄₀][k₂₇] == C₇₆[i₆₂][j₃₄₀][k₂₇])
                        && (k₂₉ < 1800
                           ==> false)
                        && j₃₄₀ < 1500)))
        && j₇₇ < 1500
        && 0 <= k₈₃
        && (forall k₂₇: int ::
              (  0 <= k₂₇
                && k₂₇ < k₈₃
                 ==> k₂₇ < 1800
                  && C₈₂[i₆₂][j₇₇][k₂₇] == B₅₆[i₆₂][j₇₇][k₂₇] + A₅₈[i₆₂][j₇₇][k₂₇]))
        && (forall k₂₇: int ::
                  0 <= k₂₇
                  && k₂₇ < k₈₃
                || C₈₂[i₆₂][j₇₇][k₂₇] == C₇₆[i₆₂][j₇₇][k₂₇])
        && 0 <= j₃₁
        && j₃₁ < j₇₇ + 1
         ==> k₈₃ < 1800
          || i₅₅ < 1000
          || (exists C₂₈: [int][int][int]int, k₂₉: int ::
                  0 <= k₂₉
                  && (forall k₂₇: int ::
                        (  0 <= k₂₇
                          && k₂₇ < k₂₉
                           ==> k₂₇ < 1800
                            && C₂₈[i₆₂][j₃₁][k₂₇] == B₅₆[i₆₂][j₃₁][k₂₇] + A₅₈[i₆₂][j₃₁][k₂₇]))
                  && (forall k₂₇: int ::
                            0 <= k₂₇
                            && k₂₇ < k₂₉
                          || C₂₈[i₆₂][j₃₁][k₂₇] == C₈₂[i₆₂][j₃₁][k₂₇])
                  && (k₂₉ < 1800
                     ==> false)
                  && j₃₁ < 1500)));

goal {:named "invariant forward"} (forall i₅₅: int, B₅₆: [int][int][int]int, A₅₈: [int][int][int]int, i₆₂: int, C₇₆: [int][int][int]int, j₇₇: int, i₃₇: int ::
      (  0 <= i₅₅
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₅₅
                 ==> (exists A₁₆: [int][int][int]int, B₁₇: [int][int][int]int, j₁₈: int ::
                        0 <= j₁₈
                        && (forall j₁₄: int ::
                              (  0 <= j₁₄
                                && j₁₄ < j₁₈
                                 ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                                        0 <= k₁₂
                                        && (forall k₉: int ::
                                              (  0 <= k₉
                                                && k₉ < k₁₂
                                                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                                        0 <= nondet_uint₂₈
                                                        && nondet_uint₂₈ < 4294967296
                                                        && 0 <= nondet_uint₁₇
                                                        && nondet_uint₁₇ < 4294967296
                                                        && k₉ < 1800
                                                        && A₁₀[i₂₀][j₁₄][k₉] == nondet_uint₁₇
                                                        && B₁₁[i₂₀][j₁₄][k₉] == nondet_uint₂₈)))
                                        && (forall k₉: int ::
                                                  0 <= k₉
                                                  && k₉ < k₁₂
                                                ||   A₁₀[i₂₀][j₁₄][k₉] == A₁₆[i₂₀][j₁₄][k₉]
                                                  && B₁₁[i₂₀][j₁₄][k₉] == B₁₇[i₂₀][j₁₄][k₉])
                                        && (k₁₂ < 1800
                                           ==> false)
                                        && j₁₄ < 1500)))
                        && (j₁₈ < 1500
                           ==> false)
                        && i₂₀ < 1000)))
        && 0 <= i₆₂
        && (forall i₃₅₄: int ::
              (  0 <= i₃₅₄
                && i₃₅₄ < i₆₂
                 ==> (exists C₃₃: [int][int][int]int, j₃₄: int ::
                        0 <= j₃₄
                        && (forall j₃₁: int ::
                              (  0 <= j₃₁
                                && j₃₁ < j₃₄
                                 ==> (exists C₂₈: [int][int][int]int, k₂₉: int ::
                                        0 <= k₂₉
                                        && (forall k₂₇: int ::
                                              (  0 <= k₂₇
                                                && k₂₇ < k₂₉
                                                 ==> k₂₇ < 1800
                                                  && C₂₈[i₃₅₄][j₃₁][k₂₇] == B₅₆[i₃₅₄][j₃₁][k₂₇] + A₅₈[i₃₅₄][j₃₁][k₂₇]))
                                        && (forall k₂₇: int ::
                                                  0 <= k₂₇
                                                  && k₂₇ < k₂₉
                                                || C₂₈[i₃₅₄][j₃₁][k₂₇] == C₃₃[i₃₅₄][j₃₁][k₂₇])
                                        && (k₂₉ < 1800
                                           ==> false)
                                        && j₃₁ < 1500)))
                        && (j₃₄ < 1500
                           ==> false)
                        && i₃₅₄ < 1000)))
        && i₆₂ < 1000
        && 0 <= j₇₇
        && (forall j₃₁: int ::
              (  0 <= j₃₁
                && j₃₁ < j₇₇
                 ==> (exists C₂₈: [int][int][int]int, k₂₉: int ::
                        0 <= k₂₉
                        && (forall k₂₇: int ::
                              (  0 <= k₂₇
                                && k₂₇ < k₂₉
                                 ==> k₂₇ < 1800
                                  && C₂₈[i₆₂][j₃₁][k₂₇] == B₅₆[i₆₂][j₃₁][k₂₇] + A₅₈[i₆₂][j₃₁][k₂₇]))
                        && (forall k₂₇: int ::
                                  0 <= k₂₇
                                  && k₂₇ < k₂₉
                                || C₂₈[i₆₂][j₃₁][k₂₇] == C₇₆[i₆₂][j₃₁][k₂₇])
                        && (k₂₉ < 1800
                           ==> false)
                        && j₃₁ < 1500)))
        && 0 <= i₃₇
        && i₃₇ < i₆₂ + 1
         ==> j₇₇ < 1500
          || i₅₅ < 1000
          || (exists C₃₃: [int][int][int]int, j₃₄: int ::
                  0 <= j₃₄
                  && (forall j₃₁: int ::
                        (  0 <= j₃₁
                          && j₃₁ < j₃₄
                           ==> (exists C₂₈: [int][int][int]int, k₂₉: int ::
                                  0 <= k₂₉
                                  && (forall k₂₇: int ::
                                        (  0 <= k₂₇
                                          && k₂₇ < k₂₉
                                           ==> k₂₇ < 1800
                                            && C₂₈[i₃₇][j₃₁][k₂₇] == B₅₆[i₃₇][j₃₁][k₂₇] + A₅₈[i₃₇][j₃₁][k₂₇]))
                                  && (forall k₂₇: int ::
                                            0 <= k₂₇
                                            && k₂₇ < k₂₉
                                          || C₂₈[i₃₇][j₃₁][k₂₇] == C₃₃[i₃₇][j₃₁][k₂₇])
                                  && (k₂₉ < 1800
                                     ==> false)
                                  && j₃₁ < 1500)))
                  && (j₃₄ < 1500
                     ==> false)
                  && i₃₇ < 1000)));

goal {:named "assert"} (forall i₅₅: int, B₅₆: [int][int][int]int, A₅₈: [int][int][int]int, C₆₁: [int][int][int]int, i₆₂: int, i₆₅: int, j₆₇: int, k₇₁: int ::
      (  0 <= i₅₅
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₅₅
                 ==> (exists A₁₆: [int][int][int]int, B₁₇: [int][int][int]int, j₁₈: int ::
                        0 <= j₁₈
                        && (forall j₁₄: int ::
                              (  0 <= j₁₄
                                && j₁₄ < j₁₈
                                 ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                                        0 <= k₁₂
                                        && (forall k₉: int ::
                                              (  0 <= k₉
                                                && k₉ < k₁₂
                                                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                                        0 <= nondet_uint₂₈
                                                        && nondet_uint₂₈ < 4294967296
                                                        && 0 <= nondet_uint₁₇
                                                        && nondet_uint₁₇ < 4294967296
                                                        && k₉ < 1800
                                                        && A₁₀[i₂₀][j₁₄][k₉] == nondet_uint₁₇
                                                        && B₁₁[i₂₀][j₁₄][k₉] == nondet_uint₂₈)))
                                        && (forall k₉: int ::
                                                  0 <= k₉
                                                  && k₉ < k₁₂
                                                ||   A₁₀[i₂₀][j₁₄][k₉] == A₁₆[i₂₀][j₁₄][k₉]
                                                  && B₁₁[i₂₀][j₁₄][k₉] == B₁₇[i₂₀][j₁₄][k₉])
                                        && (k₁₂ < 1800
                                           ==> false)
                                        && j₁₄ < 1500)))
                        && (j₁₈ < 1500
                           ==> false)
                        && i₂₀ < 1000)))
        && 0 <= i₆₂
        && (forall i₃₇: int ::
              (  0 <= i₃₇
                && i₃₇ < i₆₂
                 ==> (exists C₃₃: [int][int][int]int, j₃₄: int ::
                        0 <= j₃₄
                        && (forall j₃₁: int ::
                              (  0 <= j₃₁
                                && j₃₁ < j₃₄
                                 ==> (exists C₂₈: [int][int][int]int, k₂₉: int ::
                                        0 <= k₂₉
                                        && (forall k₂₇: int ::
                                              (  0 <= k₂₇
                                                && k₂₇ < k₂₉
                                                 ==> k₂₇ < 1800
                                                  && C₂₈[i₃₇][j₃₁][k₂₇] == B₅₆[i₃₇][j₃₁][k₂₇] + A₅₈[i₃₇][j₃₁][k₂₇]))
                                        && (forall k₂₇: int ::
                                                  0 <= k₂₇
                                                  && k₂₇ < k₂₉
                                                || C₂₈[i₃₇][j₃₁][k₂₇] == C₃₃[i₃₇][j₃₁][k₂₇])
                                        && (k₂₉ < 1800
                                           ==> false)
                                        && j₃₁ < 1500)))
                        && (j₃₄ < 1500
                           ==> false)
                        && i₃₇ < 1000)))
        && 0 <= i₆₅
        && (forall i₅₀: int ::
              (  0 <= i₅₀
                && i₅₀ < i₆₅
                 ==> (exists j₄₇: int ::
                        0 <= j₄₇
                        && (forall j₄₅: int ::
                              (  0 <= j₄₅
                                && j₄₅ < j₄₇
                                 ==> (exists k₄₃: int ::
                                        0 <= k₄₃
                                        && (forall k₄₂: int ::
                                              (  0 <= k₄₂
                                                && k₄₂ < k₄₃
                                                 ==> k₄₂ < 1800))
                                        && (k₄₃ < 1800
                                           ==> false)
                                        && j₄₅ < 1500)))
                        && (j₄₇ < 1500
                           ==> false)
                        && i₅₀ < 1000)))
        && i₆₅ < 1000
        && 0 <= j₆₇
        && (forall j₄₅: int ::
              (  0 <= j₄₅
                && j₄₅ < j₆₇
                 ==> (exists k₄₃: int ::
                        0 <= k₄₃
                        && (forall k₄₂: int ::
                              (  0 <= k₄₂
                                && k₄₂ < k₄₃
                                 ==> k₄₂ < 1800))
                        && (k₄₃ < 1800
                           ==> false)
                        && j₄₅ < 1500)))
        && j₆₇ < 1500
        && 0 <= k₇₁
        && (forall k₄₂: int ::
              (  0 <= k₄₂
                && k₄₂ < k₇₁
                 ==> k₄₂ < 1800))
        && k₇₁ < 1800
         ==> i₆₂ < 1000
          || i₅₅ < 1000
          || C₆₁[i₆₅][j₆₇][k₇₁] == A₅₈[i₆₅][j₆₇][k₇₁] + B₅₆[i₆₅][j₆₇][k₇₁]));

