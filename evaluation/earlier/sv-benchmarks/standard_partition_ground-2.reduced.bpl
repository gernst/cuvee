data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, bb: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, b₈: int, a₉: int ::
      (  0 <= i₂₂
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
        && (forall b₁₈₆: int, a₁₈₅: int ::
              (  0 <= b₁₈₆
                && b₁₈₆ < b₂₄
                && 0 <= a₁₈₅
                && a₁₈₅ < a₂₅
                 ==> 0 <= aa₂₁[a₁₈₅]
                    && a₁₈₅ < 100000
                    && bb₂₃[b₁₈₆] == aa₂₁[a₁₈₅]
                  ||   (0 <= aa₂₁[a₁₈₅]
                       ==> false)
                    && a₁₈₅ < 100000))
        && (forall b₁₈₈: int, a₁₈₇: int ::
                  0 <= b₁₈₈
                  && b₁₈₈ < b₂₄
                  && 0 <= a₁₈₇
                  && a₁₈₇ < a₂₅
                || bb₂₃[b₁₈₈] == bb[b₁₈₈])
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
        && (forall b₂₂₄: int, a₂₂₃: int ::
              (  0 <= b₂₂₄
                && b₂₂₄ < b₂₄
                && 0 <= a₂₂₃
                && a₂₂₃ < a₂₅
                 ==> 0 <= aa₂₁[a₂₂₃]
                    && a₂₂₃ < 100000
                    && bb₂₃[b₂₂₄] == aa₂₁[a₂₂₃]
                  ||   (0 <= aa₂₁[a₂₂₃]
                       ==> false)
                    && a₂₂₃ < 100000))
        && (forall b₂₂₆: int, a₂₂₅: int ::
                  0 <= b₂₂₆
                  && b₂₂₆ < b₂₄
                  && 0 <= a₂₂₅
                  && a₂₂₅ < a₂₅
                || bb₂₃[b₂₂₆] == bb[b₂₂₆])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> 0 <= a₉
          || i₂₂ < 100000
          || bb₂₃[b₂₄ := aa₂₁[a₂₅]][b₈] == bb[b₈]));

goal (forall aa: [int]int, bb: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, b₈: int, a₉: int ::
      (  0 <= i₂₂
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
         ==> a₉ < a₂₅ + 1
          || i₂₂ < 100000
          || bb₂₃[b₂₄ := aa₂₁[a₂₅]][b₈] == bb[b₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, cc₂₆: [int]int, c₂₇: int, a₂₈: int, c₁₃: int, a₁₄: int ::
      (  0 <= i₂₂
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
        && (forall c₅₃₀: int, a₅₃₁: int ::
              (  0 <= c₅₃₀
                && c₅₃₀ < c₂₇
                && 0 <= a₅₃₁
                && a₅₃₁ < a₂₈
                 ==> aa₂₁[a₅₃₁] < 0
                    && a₅₃₁ < 100000
                    && cc₂₆[c₅₃₀] == aa₂₁[a₅₃₁]
                  ||   (aa₂₁[a₅₃₁] < 0
                       ==> false)
                    && a₅₃₁ < 100000))
        && (forall c₅₃₂: int, a₅₃₃: int ::
                  0 <= c₅₃₂
                  && c₅₃₂ < c₂₇
                  && 0 <= a₅₃₃
                  && a₅₃₃ < a₂₈
                || cc₂₆[c₅₃₂] == cc[c₅₃₂])
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
        && (forall c₅₈₄: int, a₅₈₅: int ::
              (  0 <= c₅₈₄
                && c₅₈₄ < c₂₇
                && 0 <= a₅₈₅
                && a₅₈₅ < a₂₈
                 ==> aa₂₁[a₅₈₅] < 0
                    && a₅₈₅ < 100000
                    && cc₂₆[c₅₈₄] == aa₂₁[a₅₈₅]
                  ||   (aa₂₁[a₅₈₅] < 0
                       ==> false)
                    && a₅₈₅ < 100000))
        && (forall c₅₈₆: int, a₅₈₇: int ::
                  0 <= c₅₈₆
                  && c₅₈₆ < c₂₇
                  && 0 <= a₅₈₇
                  && a₅₈₇ < a₂₈
                || cc₂₆[c₅₈₆] == cc[c₅₈₆])
        && a₂₈ < 100000
        && aa₂₁[a₂₈] < 0
         ==> 0 <= a₁₄
          || a₂₅ < 100000
          || i₂₂ < 100000
          || cc₂₆[c₂₇ := aa₂₁[a₂₈]][c₁₃] == cc[c₁₃]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, bb₂₃: [int]int, b₂₄: int, a₂₅: int, cc₂₆: [int]int, c₂₇: int, a₂₈: int, c₁₃: int, a₁₄: int ::
      (  0 <= i₂₂
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
        && (forall c₆₀₁: int, a₆₀₂: int ::
              (  0 <= c₆₀₁
                && c₆₀₁ < c₂₇
                && 0 <= a₆₀₂
                && a₆₀₂ < a₂₈
                 ==> aa₂₁[a₆₀₂] < 0
                    && a₆₀₂ < 100000
                    && cc₂₆[c₆₀₁] == aa₂₁[a₆₀₂]
                  ||   (aa₂₁[a₆₀₂] < 0
                       ==> false)
                    && a₆₀₂ < 100000))
        && (forall c₆₀₃: int, a₆₀₄: int ::
                  0 <= c₆₀₃
                  && c₆₀₃ < c₂₇
                  && 0 <= a₆₀₄
                  && a₆₀₄ < a₂₈
                || cc₂₆[c₆₀₃] == cc[c₆₀₃])
        && a₂₈ < 100000
        && aa₂₁[a₂₈] < 0
         ==> a₁₄ < a₂₈ + 1
          || a₂₅ < 100000
          || i₂₂ < 100000
          || cc₂₆[c₂₇ := aa₂₁[a₂₈]][c₁₃] == cc[c₁₃]));

