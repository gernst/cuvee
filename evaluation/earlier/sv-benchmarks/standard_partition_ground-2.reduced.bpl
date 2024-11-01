data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 + b₂₄ == 0 + a₂₅
        && 0 <= b₂₄
        && 0 <= a₂₅
        && (forall b₈: int, a₉: int ::
              (  b₈ + b₈ == a₉ + a₉
                && 0 <= b₈
                && b₈ < b₂₄
                && 0 <= a₉
                && a₉ < a₂₅
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₃[b₈] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000))
        && (forall b₈: int, a₉: int ::
              (b₈ + b₈ == a₉ + a₉
                 ==> 0 <= b₈
                    && b₈ < b₂₄
                    && 0 <= a₉
                    && a₉ < a₂₅
                  || bb₂₃[b₈] == bb[b₈]))
        && a₂₅ < 100000
         ==> 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || 0 + b₂₄ == 0 + a₂₅ + 1));

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, cc₂₆: [int]int, c₂₇: int, a₂₈: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 + b₂₄ == 0 + a₂₅
        && 0 <= b₂₄
        && 0 <= a₂₅
        && (forall b₈: int, a₉: int ::
              (  b₈ + b₈ == a₉ + a₉
                && 0 <= b₈
                && b₈ < b₂₄
                && 0 <= a₉
                && a₉ < a₂₅
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₃[b₈] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000))
        && (forall b₈: int, a₉: int ::
              (b₈ + b₈ == a₉ + a₉
                 ==> 0 <= b₈
                    && b₈ < b₂₄
                    && 0 <= a₉
                    && a₉ < a₂₅
                  || bb₂₃[b₈] == bb[b₈]))
        && c₂₇ + 0 == 0 + a₂₈
        && 0 <= c₂₇
        && 0 <= a₂₈
        && (forall c₁₃: int, a₁₄: int ::
              (  c₁₃ + c₁₃ == a₁₄ + a₁₄
                && 0 <= c₁₃
                && c₁₃ < c₂₇
                && 0 <= a₁₄
                && a₁₄ < a₂₈
                 ==> aa₂₁[a₁₄] < 0
                    && a₁₄ < 100000
                    && cc₂₆[c₁₃] == aa₂₁[a₁₄]
                  ||   (aa₂₁[a₁₄] < 0
                       ==> false)
                    && a₁₄ < 100000))
        && (forall c₁₃: int, a₁₄: int ::
              (c₁₃ + c₁₃ == a₁₄ + a₁₄
                 ==> 0 <= c₁₃
                    && c₁₃ < c₂₇
                    && 0 <= a₁₄
                    && a₁₄ < a₂₈
                  || cc₂₆[c₁₃] == cc[c₁₃]))
        && a₂₈ < 100000
         ==> aa₂₁[a₂₈] < 0
          || a₂₅ < 100000
          || i₂₂ < 100000
          || c₂₇ + 0 == 0 + a₂₈ + 1));

goal {:named "assert"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, cc₂₆: [int]int, c₂₇: int, a₂₈: int, x₂₉: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 + b₂₄ == 0 + a₂₅
        && 0 <= b₂₄
        && 0 <= a₂₅
        && (forall b₈: int, a₉: int ::
              (  b₈ + b₈ == a₉ + a₉
                && 0 <= b₈
                && b₈ < b₂₄
                && 0 <= a₉
                && a₉ < a₂₅
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₃[b₈] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000))
        && (forall b₈: int, a₉: int ::
              (b₈ + b₈ == a₉ + a₉
                 ==> 0 <= b₈
                    && b₈ < b₂₄
                    && 0 <= a₉
                    && a₉ < a₂₅
                  || bb₂₃[b₈] == bb[b₈]))
        && c₂₇ + 0 == 0 + a₂₈
        && 0 <= c₂₇
        && 0 <= a₂₈
        && (forall c₁₃: int, a₁₄: int ::
              (  c₁₃ + c₁₃ == a₁₄ + a₁₄
                && 0 <= c₁₃
                && c₁₃ < c₂₇
                && 0 <= a₁₄
                && a₁₄ < a₂₈
                 ==> aa₂₁[a₁₄] < 0
                    && a₁₄ < 100000
                    && cc₂₆[c₁₃] == aa₂₁[a₁₄]
                  ||   (aa₂₁[a₁₄] < 0
                       ==> false)
                    && a₁₄ < 100000))
        && (forall c₁₃: int, a₁₄: int ::
              (c₁₃ + c₁₃ == a₁₄ + a₁₄
                 ==> 0 <= c₁₃
                    && c₁₃ < c₂₇
                    && 0 <= a₁₄
                    && a₁₄ < a₂₈
                  || cc₂₆[c₁₃] == cc[c₁₃]))
        && 0 <= x₂₉
        && (forall x₁₉: int ::
              (  0 <= x₁₉
                && x₁₉ < x₂₉
                 ==> x₁₉ < b₂₄))
        && x₂₉ < b₂₄
         ==> a₂₈ < 100000
          || a₂₅ < 100000
          || i₂₂ < 100000
          || 0 <= bb₂₃[x₂₉]));

