data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, bb: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, b₈: int, a₉: int ::
      (  0 <= i₂₂
        && i₂₂ <= 100000
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == __VERIFIER_nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 <= b₂₄
        && 0 <= a₂₅
        && a₂₅ <= 100000
        && (forall b₁₉₉: int, a₁₉₈: int ::
              (  0 <= b₁₉₉
                && b₁₉₉ < b₂₄
                && 0 <= a₁₉₈
                && a₁₉₈ < a₂₅
                 ==> 0 <= aa₂₁[a₁₉₈]
                    && a₁₉₈ < 100000
                    && bb₂₃[b₁₉₉] == aa₂₁[a₁₉₈]
                  ||   (0 <= aa₂₁[a₁₉₈]
                       ==> false)
                    && a₁₉₈ < 100000))
        && (forall b₂₀₁: int, a₂₀₀: int ::
                  0 <= b₂₀₁
                  && b₂₀₁ < b₂₄
                  && 0 <= a₂₀₀
                  && a₂₀₀ < a₂₅
                || bb₂₃[b₂₀₁] == bb[b₂₀₁])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && 0 <= b₈
        && b₈ < b₂₄ + 1
        && 0 <= a₉
        && a₉ < a₂₅ + 1
        && 0 <= aa₂₁[a₉]
         ==> i₂₂ < 100000
          || bb₂₃[b₂₄ := aa₂₁[a₂₅]][b₈] == aa₂₁[a₉]));

goal (forall aa: [int]int, bb: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, b₈: int, a₉: int ::
      (  0 <= i₂₂
        && i₂₂ <= 100000
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == __VERIFIER_nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 <= b₂₄
        && 0 <= a₂₅
        && a₂₅ <= 100000
        && (forall b₂₃₇: int, a₂₃₆: int ::
              (  0 <= b₂₃₇
                && b₂₃₇ < b₂₄
                && 0 <= a₂₃₆
                && a₂₃₆ < a₂₅
                 ==> 0 <= aa₂₁[a₂₃₆]
                    && a₂₃₆ < 100000
                    && bb₂₃[b₂₃₇] == aa₂₁[a₂₃₆]
                  ||   (0 <= aa₂₁[a₂₃₆]
                       ==> false)
                    && a₂₃₆ < 100000))
        && (forall b₂₃₉: int, a₂₃₈: int ::
                  0 <= b₂₃₉
                  && b₂₃₉ < b₂₄
                  && 0 <= a₂₃₈
                  && a₂₃₈ < a₂₅
                || bb₂₃[b₂₃₉] == bb[b₂₃₉])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> 0 <= a₉
          || i₂₂ < 100000
          || bb₂₃[b₂₄ := aa₂₁[a₂₅]][b₈] == bb[b₈]));

goal (forall aa: [int]int, bb: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, b₈: int, a₉: int ::
      (  0 <= i₂₂
        && i₂₂ <= 100000
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == __VERIFIER_nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 <= b₂₄
        && 0 <= a₂₅
        && a₂₅ <= 100000
        && (forall b₂₅₀: int, a₂₄₉: int ::
              (  0 <= b₂₅₀
                && b₂₅₀ < b₂₄
                && 0 <= a₂₄₉
                && a₂₄₉ < a₂₅
                 ==> 0 <= aa₂₁[a₂₄₉]
                    && a₂₄₉ < 100000
                    && bb₂₃[b₂₅₀] == aa₂₁[a₂₄₉]
                  ||   (0 <= aa₂₁[a₂₄₉]
                       ==> false)
                    && a₂₄₉ < 100000))
        && (forall b₂₅₂: int, a₂₅₁: int ::
                  0 <= b₂₅₂
                  && b₂₅₂ < b₂₄
                  && 0 <= a₂₅₁
                  && a₂₅₁ < a₂₅
                || bb₂₃[b₂₅₂] == bb[b₂₅₂])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> a₉ < a₂₅ + 1
          || i₂₂ < 100000
          || bb₂₃[b₂₄ := aa₂₁[a₂₅]][b₈] == bb[b₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, cc₂₆: [int]int, c₂₇: int, a₂₈: int, c₁₃: int, a₁₄: int ::
      (  0 <= i₂₂
        && i₂₂ <= 100000
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == __VERIFIER_nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 <= b₂₄
        && 0 <= a₂₅
        && a₂₅ <= 100000
        && (forall b₈: int, a₉: int ::
              (  0 <= b₈
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
                  0 <= b₈
                  && b₈ < b₂₄
                  && 0 <= a₉
                  && a₉ < a₂₅
                || bb₂₃[b₈] == bb[b₈])
        && 0 <= c₂₇
        && 0 <= a₂₈
        && a₂₈ <= 100000
        && (forall c₅₆₈: int, a₅₆₉: int ::
              (  0 <= c₅₆₈
                && c₅₆₈ < c₂₇
                && 0 <= a₅₆₉
                && a₅₆₉ < a₂₈
                 ==> aa₂₁[a₅₆₉] < 0
                    && a₅₆₉ < 100000
                    && cc₂₆[c₅₆₈] == aa₂₁[a₅₆₉]
                  ||   (aa₂₁[a₅₆₉] < 0
                       ==> false)
                    && a₅₆₉ < 100000))
        && (forall c₅₇₀: int, a₅₇₁: int ::
                  0 <= c₅₇₀
                  && c₅₇₀ < c₂₇
                  && 0 <= a₅₇₁
                  && a₅₇₁ < a₂₈
                || cc₂₆[c₅₇₀] == cc[c₅₇₀])
        && a₂₈ < 100000
        && aa₂₁[a₂₈] < 0
        && 0 <= c₁₃
        && c₁₃ < c₂₇ + 1
        && 0 <= a₁₄
        && a₁₄ < a₂₈ + 1
        && aa₂₁[a₁₄] < 0
         ==> a₂₅ < 100000
          || i₂₂ < 100000
          || cc₂₆[c₂₇ := aa₂₁[a₂₈]][c₁₃] == aa₂₁[a₁₄]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, cc₂₆: [int]int, c₂₇: int, a₂₈: int, c₁₃: int, a₁₄: int ::
      (  0 <= i₂₂
        && i₂₂ <= 100000
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == __VERIFIER_nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 <= b₂₄
        && 0 <= a₂₅
        && a₂₅ <= 100000
        && (forall b₈: int, a₉: int ::
              (  0 <= b₈
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
                  0 <= b₈
                  && b₈ < b₂₄
                  && 0 <= a₉
                  && a₉ < a₂₅
                || bb₂₃[b₈] == bb[b₈])
        && 0 <= c₂₇
        && 0 <= a₂₈
        && a₂₈ <= 100000
        && (forall c₆₂₂: int, a₆₂₃: int ::
              (  0 <= c₆₂₂
                && c₆₂₂ < c₂₇
                && 0 <= a₆₂₃
                && a₆₂₃ < a₂₈
                 ==> aa₂₁[a₆₂₃] < 0
                    && a₆₂₃ < 100000
                    && cc₂₆[c₆₂₂] == aa₂₁[a₆₂₃]
                  ||   (aa₂₁[a₆₂₃] < 0
                       ==> false)
                    && a₆₂₃ < 100000))
        && (forall c₆₂₄: int, a₆₂₅: int ::
                  0 <= c₆₂₄
                  && c₆₂₄ < c₂₇
                  && 0 <= a₆₂₅
                  && a₆₂₅ < a₂₈
                || cc₂₆[c₆₂₄] == cc[c₆₂₄])
        && a₂₈ < 100000
        && aa₂₁[a₂₈] < 0
         ==> 0 <= a₁₄
          || a₂₅ < 100000
          || i₂₂ < 100000
          || cc₂₆[c₂₇ := aa₂₁[a₂₈]][c₁₃] == cc[c₁₃]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, cc₂₆: [int]int, c₂₇: int, a₂₈: int, c₁₃: int, a₁₄: int ::
      (  0 <= i₂₂
        && i₂₂ <= 100000
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == __VERIFIER_nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 <= b₂₄
        && 0 <= a₂₅
        && a₂₅ <= 100000
        && (forall b₈: int, a₉: int ::
              (  0 <= b₈
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
                  0 <= b₈
                  && b₈ < b₂₄
                  && 0 <= a₉
                  && a₉ < a₂₅
                || bb₂₃[b₈] == bb[b₈])
        && 0 <= c₂₇
        && 0 <= a₂₈
        && a₂₈ <= 100000
        && (forall c₆₃₉: int, a₆₄₀: int ::
              (  0 <= c₆₃₉
                && c₆₃₉ < c₂₇
                && 0 <= a₆₄₀
                && a₆₄₀ < a₂₈
                 ==> aa₂₁[a₆₄₀] < 0
                    && a₆₄₀ < 100000
                    && cc₂₆[c₆₃₉] == aa₂₁[a₆₄₀]
                  ||   (aa₂₁[a₆₄₀] < 0
                       ==> false)
                    && a₆₄₀ < 100000))
        && (forall c₆₄₁: int, a₆₄₂: int ::
                  0 <= c₆₄₁
                  && c₆₄₁ < c₂₇
                  && 0 <= a₆₄₂
                  && a₆₄₂ < a₂₈
                || cc₂₆[c₆₄₁] == cc[c₆₄₁])
        && a₂₈ < 100000
        && aa₂₁[a₂₈] < 0
         ==> a₁₄ < a₂₈ + 1
          || a₂₅ < 100000
          || i₂₂ < 100000
          || cc₂₆[c₂₇ := aa₂₁[a₂₈]][c₁₃] == cc[c₁₃]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, cc₂₆: [int]int, c₂₇: int, a₂₈: int, x₂₉: int ::
      (  0 <= i₂₂
        && i₂₂ <= 100000
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists __VERIFIER_nondet_int₁₄: int ::
                        i₅ < 100000
                        && aa₂₁[i₅] == __VERIFIER_nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && 0 <= b₂₄
        && 0 <= a₂₅
        && a₂₅ <= 100000
        && (forall b₈: int, a₉: int ::
              (  0 <= b₈
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
                  0 <= b₈
                  && b₈ < b₂₄
                  && 0 <= a₉
                  && a₉ < a₂₅
                || bb₂₃[b₈] == bb[b₈])
        && 0 <= c₂₇
        && 0 <= a₂₈
        && a₂₈ <= 100000
        && (forall c₁₃: int, a₁₄: int ::
              (  0 <= c₁₃
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
                  0 <= c₁₃
                  && c₁₃ < c₂₇
                  && 0 <= a₁₄
                  && a₁₄ < a₂₈
                || cc₂₆[c₁₃] == cc[c₁₃])
        && 0 <= x₂₉
        && x₂₉ <= b₂₄
        && (forall x₁₉: int ::
              (  0 <= x₁₉
                && x₁₉ < x₂₉
                 ==> x₁₉ < b₂₄))
        && x₂₉ < b₂₄
         ==> a₂₈ < 100000
          || a₂₅ < 100000
          || i₂₂ < 100000
          || 0 <= bb₂₃[x₂₉]));

