data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₂₆₉: int, a₂₆₈: int, b₂₇₀: int ::
              (  0 <= c₂₆₉
                && c₂₆₉ < c₂₃
                && 0 <= a₂₆₈
                && a₂₆₈ < a₂₅
                && 0 <= b₂₇₀
                && b₂₇₀ < b₂₆
                 ==> 0 <= aa₂₁[a₂₆₈]
                    && a₂₆₈ < 100000
                    && bb₂₇[b₂₇₀] == aa₂₁[a₂₆₈]
                  ||   (0 <= aa₂₁[a₂₆₈]
                       ==> false)
                    && a₂₆₈ < 100000
                    && cc₂₄[c₂₆₉] == aa₂₁[a₂₆₈]))
        && (forall c₂₇₂: int, a₂₇₁: int, b₂₇₃: int ::
                  0 <= c₂₇₂
                  && c₂₇₂ < c₂₃
                  && 0 <= a₂₇₁
                  && a₂₇₁ < a₂₅
                  && 0 <= b₂₇₃
                  && b₂₇₃ < b₂₆
                ||   bb₂₇[b₂₇₃] == bb[b₂₇₃]
                  && cc₂₄[c₂₇₂] == cc[c₂₇₂])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && 0 <= c₈
        && c₈ < c₂₃
        && 0 <= a₉
        && a₉ < a₂₅ + 1
        && 0 <= b₁₀
        && b₁₀ < b₂₆ + 1
         ==> i₂₂ < 100000
          || 0 <= aa₂₁[a₉]
          || cc₂₄[c₈] == aa₂₁[a₉]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₃₂₇: int, a₃₂₆: int, b₃₂₈: int ::
              (  0 <= c₃₂₇
                && c₃₂₇ < c₂₃
                && 0 <= a₃₂₆
                && a₃₂₆ < a₂₅
                && 0 <= b₃₂₈
                && b₃₂₈ < b₂₆
                 ==> 0 <= aa₂₁[a₃₂₆]
                    && a₃₂₆ < 100000
                    && bb₂₇[b₃₂₈] == aa₂₁[a₃₂₆]
                  ||   (0 <= aa₂₁[a₃₂₆]
                       ==> false)
                    && a₃₂₆ < 100000
                    && cc₂₄[c₃₂₇] == aa₂₁[a₃₂₆]))
        && (forall c₃₃₀: int, a₃₂₉: int, b₃₃₁: int ::
                  0 <= c₃₃₀
                  && c₃₃₀ < c₂₃
                  && 0 <= a₃₂₉
                  && a₃₂₉ < a₂₅
                  && 0 <= b₃₃₁
                  && b₃₃₁ < b₂₆
                ||   bb₂₇[b₃₃₁] == bb[b₃₃₁]
                  && cc₂₄[c₃₃₀] == cc[c₃₃₀])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && 0 <= c₈
        && c₈ < c₂₃
        && 0 <= a₉
        && a₉ < a₂₅ + 1
        && 0 <= b₁₀
        && b₁₀ < b₂₆ + 1
        && 0 <= aa₂₁[a₉]
         ==> i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == aa₂₁[a₉]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₃₅₉: int, a₃₅₈: int, b₃₆₀: int ::
              (  0 <= c₃₅₉
                && c₃₅₉ < c₂₃
                && 0 <= a₃₅₈
                && a₃₅₈ < a₂₅
                && 0 <= b₃₆₀
                && b₃₆₀ < b₂₆
                 ==> 0 <= aa₂₁[a₃₅₈]
                    && a₃₅₈ < 100000
                    && bb₂₇[b₃₆₀] == aa₂₁[a₃₅₈]
                  ||   (0 <= aa₂₁[a₃₅₈]
                       ==> false)
                    && a₃₅₈ < 100000
                    && cc₂₄[c₃₅₉] == aa₂₁[a₃₅₈]))
        && (forall c₃₆₂: int, a₃₆₁: int, b₃₆₃: int ::
                  0 <= c₃₆₂
                  && c₃₆₂ < c₂₃
                  && 0 <= a₃₆₁
                  && a₃₆₁ < a₂₅
                  && 0 <= b₃₆₃
                  && b₃₆₃ < b₂₆
                ||   bb₂₇[b₃₆₃] == bb[b₃₆₃]
                  && cc₂₄[c₃₆₂] == cc[c₃₆₂])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && 0 <= c₈
        && c₈ < c₂₃
        && 0 <= a₉
        && a₉ < a₂₅ + 1
        && 0 <= b₁₀
        && b₁₀ < b₂₆ + 1
         ==> i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == aa₂₁[a₉]
          || cc₂₄[c₈] == aa₂₁[a₉]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₃₇₆: int, a₉: int, b₃₇₇: int ::
              (  0 <= c₃₇₆
                && c₃₇₆ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₃₇₇
                && b₃₇₇ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₃₇₇] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₃₇₆] == aa₂₁[a₉]))
        && (forall c₃₇₈: int, a₉: int, b₃₇₉: int ::
                  0 <= c₃₇₈
                  && c₃₇₈ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₃₇₉
                  && b₃₇₉ < b₂₆
                ||   bb₂₇[b₃₇₉] == bb[b₃₇₉]
                  && cc₂₄[c₃₇₈] == cc[c₃₇₈])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> 0 <= c₈
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₄₀₃: int, a₉: int, b₄₀₄: int ::
              (  0 <= c₄₀₃
                && c₄₀₃ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₄₀₄
                && b₄₀₄ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₄₀₄] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₄₀₃] == aa₂₁[a₉]))
        && (forall c₄₀₅: int, a₉: int, b₄₀₆: int ::
                  0 <= c₄₀₅
                  && c₄₀₅ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₄₀₆
                  && b₄₀₆ < b₂₆
                ||   bb₂₇[b₄₀₆] == bb[b₄₀₆]
                  && cc₂₄[c₄₀₅] == cc[c₄₀₅])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> c₈ < c₂₃
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₄₃₀: int, b₄₃₁: int ::
              (  0 <= c₈
                && c₈ < c₂₃
                && 0 <= a₄₃₀
                && a₄₃₀ < a₂₅
                && 0 <= b₄₃₁
                && b₄₃₁ < b₂₆
                 ==> 0 <= aa₂₁[a₄₃₀]
                    && a₄₃₀ < 100000
                    && bb₂₇[b₄₃₁] == aa₂₁[a₄₃₀]
                  ||   (0 <= aa₂₁[a₄₃₀]
                       ==> false)
                    && a₄₃₀ < 100000
                    && cc₂₄[c₈] == aa₂₁[a₄₃₀]))
        && (forall c₈: int, a₄₃₂: int, b₄₃₃: int ::
                  0 <= c₈
                  && c₈ < c₂₃
                  && 0 <= a₄₃₂
                  && a₄₃₂ < a₂₅
                  && 0 <= b₄₃₃
                  && b₄₃₃ < b₂₆
                ||   bb₂₇[b₄₃₃] == bb[b₄₃₃]
                  && cc₂₄[c₈] == cc[c₈])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> 0 <= a₉
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₄₅₈: int, b₄₅₉: int ::
              (  0 <= c₈
                && c₈ < c₂₃
                && 0 <= a₄₅₈
                && a₄₅₈ < a₂₅
                && 0 <= b₄₅₉
                && b₄₅₉ < b₂₆
                 ==> 0 <= aa₂₁[a₄₅₈]
                    && a₄₅₈ < 100000
                    && bb₂₇[b₄₅₉] == aa₂₁[a₄₅₈]
                  ||   (0 <= aa₂₁[a₄₅₈]
                       ==> false)
                    && a₄₅₈ < 100000
                    && cc₂₄[c₈] == aa₂₁[a₄₅₈]))
        && (forall c₈: int, a₄₆₀: int, b₄₆₁: int ::
                  0 <= c₈
                  && c₈ < c₂₃
                  && 0 <= a₄₆₀
                  && a₄₆₀ < a₂₅
                  && 0 <= b₄₆₁
                  && b₄₆₁ < b₂₆
                ||   bb₂₇[b₄₆₁] == bb[b₄₆₁]
                  && cc₂₄[c₈] == cc[c₈])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> a₉ < a₂₅ + 1
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₅₉₀: int, a₅₈₉: int, b₅₉₁: int ::
              (  0 <= c₅₉₀
                && c₅₉₀ < c₂₃
                && 0 <= a₅₈₉
                && a₅₈₉ < a₂₅
                && 0 <= b₅₉₁
                && b₅₉₁ < b₂₆
                 ==> 0 <= aa₂₁[a₅₈₉]
                    && a₅₈₉ < 100000
                    && bb₂₇[b₅₉₁] == aa₂₁[a₅₈₉]
                  ||   (0 <= aa₂₁[a₅₈₉]
                       ==> false)
                    && a₅₈₉ < 100000
                    && cc₂₄[c₅₉₀] == aa₂₁[a₅₈₉]))
        && (forall c₅₉₃: int, a₅₉₂: int, b₅₉₄: int ::
                  0 <= c₅₉₃
                  && c₅₉₃ < c₂₃
                  && 0 <= a₅₉₂
                  && a₅₉₂ < a₂₅
                  && 0 <= b₅₉₄
                  && b₅₉₄ < b₂₆
                ||   bb₂₇[b₅₉₄] == bb[b₅₉₄]
                  && cc₂₄[c₅₉₃] == cc[c₅₉₃])
        && a₂₅ < 100000
        && 0 <= c₈
        && c₈ < c₂₃ + 1
        && 0 <= a₉
        && a₉ < a₂₅ + 1
        && 0 <= b₁₀
        && b₁₀ < b₂₆
         ==> 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || 0 <= aa₂₁[a₉]
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == aa₂₁[a₉]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₆₄₈: int, a₆₄₇: int, b₆₄₉: int ::
              (  0 <= c₆₄₈
                && c₆₄₈ < c₂₃
                && 0 <= a₆₄₇
                && a₆₄₇ < a₂₅
                && 0 <= b₆₄₉
                && b₆₄₉ < b₂₆
                 ==> 0 <= aa₂₁[a₆₄₇]
                    && a₆₄₇ < 100000
                    && bb₂₇[b₆₄₉] == aa₂₁[a₆₄₇]
                  ||   (0 <= aa₂₁[a₆₄₇]
                       ==> false)
                    && a₆₄₇ < 100000
                    && cc₂₄[c₆₄₈] == aa₂₁[a₆₄₇]))
        && (forall c₆₅₁: int, a₆₅₀: int, b₆₅₂: int ::
                  0 <= c₆₅₁
                  && c₆₅₁ < c₂₃
                  && 0 <= a₆₅₀
                  && a₆₅₀ < a₂₅
                  && 0 <= b₆₅₂
                  && b₆₅₂ < b₂₆
                ||   bb₂₇[b₆₅₂] == bb[b₆₅₂]
                  && cc₂₄[c₆₅₁] == cc[c₆₅₁])
        && a₂₅ < 100000
        && 0 <= c₈
        && c₈ < c₂₃ + 1
        && 0 <= a₉
        && a₉ < a₂₅ + 1
        && 0 <= b₁₀
        && b₁₀ < b₂₆
        && 0 <= aa₂₁[a₉]
         ==> 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || bb₂₇[b₁₀] == aa₂₁[a₉]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₆₈₀: int, a₆₇₉: int, b₆₈₁: int ::
              (  0 <= c₆₈₀
                && c₆₈₀ < c₂₃
                && 0 <= a₆₇₉
                && a₆₇₉ < a₂₅
                && 0 <= b₆₈₁
                && b₆₈₁ < b₂₆
                 ==> 0 <= aa₂₁[a₆₇₉]
                    && a₆₇₉ < 100000
                    && bb₂₇[b₆₈₁] == aa₂₁[a₆₇₉]
                  ||   (0 <= aa₂₁[a₆₇₉]
                       ==> false)
                    && a₆₇₉ < 100000
                    && cc₂₄[c₆₈₀] == aa₂₁[a₆₇₉]))
        && (forall c₆₈₃: int, a₆₈₂: int, b₆₈₄: int ::
                  0 <= c₆₈₃
                  && c₆₈₃ < c₂₃
                  && 0 <= a₆₈₂
                  && a₆₈₂ < a₂₅
                  && 0 <= b₆₈₄
                  && b₆₈₄ < b₂₆
                ||   bb₂₇[b₆₈₄] == bb[b₆₈₄]
                  && cc₂₄[c₆₈₃] == cc[c₆₈₃])
        && a₂₅ < 100000
        && 0 <= c₈
        && c₈ < c₂₃ + 1
        && 0 <= a₉
        && a₉ < a₂₅ + 1
        && 0 <= b₁₀
        && b₁₀ < b₂₆
         ==> 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || bb₂₇[b₁₀] == aa₂₁[a₉]
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == aa₂₁[a₉]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₇₅₆: int, a₇₅₅: int, b₁₀: int ::
              (  0 <= c₇₅₆
                && c₇₅₆ < c₂₃
                && 0 <= a₇₅₅
                && a₇₅₅ < a₂₅
                && 0 <= b₁₀
                && b₁₀ < b₂₆
                 ==> 0 <= aa₂₁[a₇₅₅]
                    && a₇₅₅ < 100000
                    && bb₂₇[b₁₀] == aa₂₁[a₇₅₅]
                  ||   (0 <= aa₂₁[a₇₅₅]
                       ==> false)
                    && a₇₅₅ < 100000
                    && cc₂₄[c₇₅₆] == aa₂₁[a₇₅₅]))
        && (forall c₇₅₈: int, a₇₅₇: int, b₁₀: int ::
                  0 <= c₇₅₈
                  && c₇₅₈ < c₂₃
                  && 0 <= a₇₅₇
                  && a₇₅₇ < a₂₅
                  && 0 <= b₁₀
                  && b₁₀ < b₂₆
                ||   bb₂₇[b₁₀] == bb[b₁₀]
                  && cc₂₄[c₇₅₈] == cc[c₇₅₈])
        && a₂₅ < 100000
         ==> 0 <= a₉
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₇₈₄: int, a₇₈₃: int, b₁₀: int ::
              (  0 <= c₇₈₄
                && c₇₈₄ < c₂₃
                && 0 <= a₇₈₃
                && a₇₈₃ < a₂₅
                && 0 <= b₁₀
                && b₁₀ < b₂₆
                 ==> 0 <= aa₂₁[a₇₈₃]
                    && a₇₈₃ < 100000
                    && bb₂₇[b₁₀] == aa₂₁[a₇₈₃]
                  ||   (0 <= aa₂₁[a₇₈₃]
                       ==> false)
                    && a₇₈₃ < 100000
                    && cc₂₄[c₇₈₄] == aa₂₁[a₇₈₃]))
        && (forall c₇₈₆: int, a₇₈₅: int, b₁₀: int ::
                  0 <= c₇₈₆
                  && c₇₈₆ < c₂₃
                  && 0 <= a₇₈₅
                  && a₇₈₅ < a₂₅
                  && 0 <= b₁₀
                  && b₁₀ < b₂₆
                ||   bb₂₇[b₁₀] == bb[b₁₀]
                  && cc₂₄[c₇₈₆] == cc[c₇₈₆])
        && a₂₅ < 100000
         ==> a₉ < a₂₅ + 1
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈₁₀: int, a₉: int, b₈₁₁: int ::
              (  0 <= c₈₁₀
                && c₈₁₀ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₈₁₁
                && b₈₁₁ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₈₁₁] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₈₁₀] == aa₂₁[a₉]))
        && (forall c₈₁₂: int, a₉: int, b₈₁₃: int ::
                  0 <= c₈₁₂
                  && c₈₁₂ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₈₁₃
                  && b₈₁₃ < b₂₆
                ||   bb₂₇[b₈₁₃] == bb[b₈₁₃]
                  && cc₂₄[c₈₁₂] == cc[c₈₁₂])
        && a₂₅ < 100000
         ==> 0 <= b₁₀
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈₃₇: int, a₉: int, b₈₃₈: int ::
              (  0 <= c₈₃₇
                && c₈₃₇ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₈₃₈
                && b₈₃₈ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₈₃₈] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₈₃₇] == aa₂₁[a₉]))
        && (forall c₈₃₉: int, a₉: int, b₈₄₀: int ::
                  0 <= c₈₃₉
                  && c₈₃₉ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₈₄₀
                  && b₈₄₀ < b₂₆
                ||   bb₂₇[b₈₄₀] == bb[b₈₄₀]
                  && cc₂₄[c₈₃₉] == cc[c₈₃₉])
        && a₂₅ < 100000
         ==> b₁₀ < b₂₆
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, x₂₈: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₉: int, b₁₀: int ::
              (  0 <= c₈
                && c₈ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₁₀
                && b₁₀ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₁₀] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₈] == aa₂₁[a₉]))
        && (forall c₈: int, a₉: int, b₁₀: int ::
                  0 <= c₈
                  && c₈ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₁₀
                  && b₁₀ < b₂₆
                ||   bb₂₇[b₁₀] == bb[b₁₀]
                  && cc₂₄[c₈] == cc[c₈])
        && 0 <= x₂₈
        && (forall x₁₇: int ::
              (  0 <= x₁₇
                && x₁₇ < x₂₈
                 ==> x₁₇ < b₂₆))
        && x₂₈ < b₂₆
         ==> a₂₅ < 100000
          || i₂₂ < 100000
          || 0 <= bb₂₇[x₂₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, x₂₈: int, x₂₉: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₉: int, b₁₀: int ::
              (  0 <= c₈
                && c₈ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₁₀
                && b₁₀ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₁₀] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₈] == aa₂₁[a₉]))
        && (forall c₈: int, a₉: int, b₁₀: int ::
                  0 <= c₈
                  && c₈ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₁₀
                  && b₁₀ < b₂₆
                ||   bb₂₇[b₁₀] == bb[b₁₀]
                  && cc₂₄[c₈] == cc[c₈])
        && 0 <= x₂₈
        && (forall x₁₇: int ::
              (  0 <= x₁₇
                && x₁₇ < x₂₈
                 ==> x₁₇ < b₂₆))
        && 0 <= x₂₉
        && (forall x₁₉: int ::
              (  0 <= x₁₉
                && x₁₉ < x₂₉
                 ==> x₁₉ < c₂₃))
        && x₂₉ < c₂₃
         ==> x₂₈ < b₂₆
          || a₂₅ < 100000
          || i₂₂ < 100000
          || cc₂₄[x₂₉] < 0));

