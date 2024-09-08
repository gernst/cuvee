data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₂₈₅: int, a₂₈₄: int, b₂₈₆: int ::
              (  0 <= c₂₈₅
                && c₂₈₅ < c₂₃
                && 0 <= a₂₈₄
                && a₂₈₄ < a₂₅
                && 0 <= b₂₈₆
                && b₂₈₆ < b₂₆
                 ==> 0 <= aa₂₁[a₂₈₄]
                    && a₂₈₄ < 100000
                    && bb₂₇[b₂₈₆] == aa₂₁[a₂₈₄]
                  ||   (0 <= aa₂₁[a₂₈₄]
                       ==> false)
                    && a₂₈₄ < 100000
                    && cc₂₄[c₂₈₅] == aa₂₁[a₂₈₄]))
        && (forall c₂₈₈: int, a₂₈₇: int, b₂₈₉: int ::
                  0 <= c₂₈₈
                  && c₂₈₈ < c₂₃
                  && 0 <= a₂₈₇
                  && a₂₈₇ < a₂₅
                  && 0 <= b₂₈₉
                  && b₂₈₉ < b₂₆
                ||   bb₂₇[b₂₈₉] == bb[b₂₈₉]
                  && cc₂₄[c₂₈₈] == cc[c₂₈₈])
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₃₄₃: int, a₃₄₂: int, b₃₄₄: int ::
              (  0 <= c₃₄₃
                && c₃₄₃ < c₂₃
                && 0 <= a₃₄₂
                && a₃₄₂ < a₂₅
                && 0 <= b₃₄₄
                && b₃₄₄ < b₂₆
                 ==> 0 <= aa₂₁[a₃₄₂]
                    && a₃₄₂ < 100000
                    && bb₂₇[b₃₄₄] == aa₂₁[a₃₄₂]
                  ||   (0 <= aa₂₁[a₃₄₂]
                       ==> false)
                    && a₃₄₂ < 100000
                    && cc₂₄[c₃₄₃] == aa₂₁[a₃₄₂]))
        && (forall c₃₄₆: int, a₃₄₅: int, b₃₄₇: int ::
                  0 <= c₃₄₆
                  && c₃₄₆ < c₂₃
                  && 0 <= a₃₄₅
                  && a₃₄₅ < a₂₅
                  && 0 <= b₃₄₇
                  && b₃₄₇ < b₂₆
                ||   bb₂₇[b₃₄₇] == bb[b₃₄₇]
                  && cc₂₄[c₃₄₆] == cc[c₃₄₆])
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₃₇₅: int, a₃₇₄: int, b₃₇₆: int ::
              (  0 <= c₃₇₅
                && c₃₇₅ < c₂₃
                && 0 <= a₃₇₄
                && a₃₇₄ < a₂₅
                && 0 <= b₃₇₆
                && b₃₇₆ < b₂₆
                 ==> 0 <= aa₂₁[a₃₇₄]
                    && a₃₇₄ < 100000
                    && bb₂₇[b₃₇₆] == aa₂₁[a₃₇₄]
                  ||   (0 <= aa₂₁[a₃₇₄]
                       ==> false)
                    && a₃₇₄ < 100000
                    && cc₂₄[c₃₇₅] == aa₂₁[a₃₇₄]))
        && (forall c₃₇₈: int, a₃₇₇: int, b₃₇₉: int ::
                  0 <= c₃₇₈
                  && c₃₇₈ < c₂₃
                  && 0 <= a₃₇₇
                  && a₃₇₇ < a₂₅
                  && 0 <= b₃₇₉
                  && b₃₇₉ < b₂₆
                ||   bb₂₇[b₃₇₉] == bb[b₃₇₉]
                  && cc₂₄[c₃₇₈] == cc[c₃₇₈])
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₃₉₂: int, a₉: int, b₃₉₃: int ::
              (  0 <= c₃₉₂
                && c₃₉₂ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₃₉₃
                && b₃₉₃ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₃₉₃] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₃₉₂] == aa₂₁[a₉]))
        && (forall c₃₉₄: int, a₉: int, b₃₉₅: int ::
                  0 <= c₃₉₄
                  && c₃₉₄ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₃₉₅
                  && b₃₉₅ < b₂₆
                ||   bb₂₇[b₃₉₅] == bb[b₃₉₅]
                  && cc₂₄[c₃₉₄] == cc[c₃₉₄])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> 0 <= c₈
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₄₁₉: int, a₉: int, b₄₂₀: int ::
              (  0 <= c₄₁₉
                && c₄₁₉ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₄₂₀
                && b₄₂₀ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₄₂₀] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₄₁₉] == aa₂₁[a₉]))
        && (forall c₄₂₁: int, a₉: int, b₄₂₂: int ::
                  0 <= c₄₂₁
                  && c₄₂₁ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₄₂₂
                  && b₄₂₂ < b₂₆
                ||   bb₂₇[b₄₂₂] == bb[b₄₂₂]
                  && cc₂₄[c₄₂₁] == cc[c₄₂₁])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> c₈ < c₂₃
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₈: int, a₄₄₆: int, b₄₄₇: int ::
              (  0 <= c₈
                && c₈ < c₂₃
                && 0 <= a₄₄₆
                && a₄₄₆ < a₂₅
                && 0 <= b₄₄₇
                && b₄₄₇ < b₂₆
                 ==> 0 <= aa₂₁[a₄₄₆]
                    && a₄₄₆ < 100000
                    && bb₂₇[b₄₄₇] == aa₂₁[a₄₄₆]
                  ||   (0 <= aa₂₁[a₄₄₆]
                       ==> false)
                    && a₄₄₆ < 100000
                    && cc₂₄[c₈] == aa₂₁[a₄₄₆]))
        && (forall c₈: int, a₄₄₈: int, b₄₄₉: int ::
                  0 <= c₈
                  && c₈ < c₂₃
                  && 0 <= a₄₄₈
                  && a₄₄₈ < a₂₅
                  && 0 <= b₄₄₉
                  && b₄₄₉ < b₂₆
                ||   bb₂₇[b₄₄₉] == bb[b₄₄₉]
                  && cc₂₄[c₈] == cc[c₈])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> 0 <= a₉
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₈: int, a₄₇₄: int, b₄₇₅: int ::
              (  0 <= c₈
                && c₈ < c₂₃
                && 0 <= a₄₇₄
                && a₄₇₄ < a₂₅
                && 0 <= b₄₇₅
                && b₄₇₅ < b₂₆
                 ==> 0 <= aa₂₁[a₄₇₄]
                    && a₄₇₄ < 100000
                    && bb₂₇[b₄₇₅] == aa₂₁[a₄₇₄]
                  ||   (0 <= aa₂₁[a₄₇₄]
                       ==> false)
                    && a₄₇₄ < 100000
                    && cc₂₄[c₈] == aa₂₁[a₄₇₄]))
        && (forall c₈: int, a₄₇₆: int, b₄₇₇: int ::
                  0 <= c₈
                  && c₈ < c₂₃
                  && 0 <= a₄₇₆
                  && a₄₇₆ < a₂₅
                  && 0 <= b₄₇₇
                  && b₄₇₇ < b₂₆
                ||   bb₂₇[b₄₇₇] == bb[b₄₇₇]
                  && cc₂₄[c₈] == cc[c₈])
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> a₉ < a₂₅ + 1
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₆₁₆: int, a₆₁₅: int, b₆₁₇: int ::
              (  0 <= c₆₁₆
                && c₆₁₆ < c₂₃
                && 0 <= a₆₁₅
                && a₆₁₅ < a₂₅
                && 0 <= b₆₁₇
                && b₆₁₇ < b₂₆
                 ==> 0 <= aa₂₁[a₆₁₅]
                    && a₆₁₅ < 100000
                    && bb₂₇[b₆₁₇] == aa₂₁[a₆₁₅]
                  ||   (0 <= aa₂₁[a₆₁₅]
                       ==> false)
                    && a₆₁₅ < 100000
                    && cc₂₄[c₆₁₆] == aa₂₁[a₆₁₅]))
        && (forall c₆₁₉: int, a₆₁₈: int, b₆₂₀: int ::
                  0 <= c₆₁₉
                  && c₆₁₉ < c₂₃
                  && 0 <= a₆₁₈
                  && a₆₁₈ < a₂₅
                  && 0 <= b₆₂₀
                  && b₆₂₀ < b₂₆
                ||   bb₂₇[b₆₂₀] == bb[b₆₂₀]
                  && cc₂₄[c₆₁₉] == cc[c₆₁₉])
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₆₇₄: int, a₆₇₃: int, b₆₇₅: int ::
              (  0 <= c₆₇₄
                && c₆₇₄ < c₂₃
                && 0 <= a₆₇₃
                && a₆₇₃ < a₂₅
                && 0 <= b₆₇₅
                && b₆₇₅ < b₂₆
                 ==> 0 <= aa₂₁[a₆₇₃]
                    && a₆₇₃ < 100000
                    && bb₂₇[b₆₇₅] == aa₂₁[a₆₇₃]
                  ||   (0 <= aa₂₁[a₆₇₃]
                       ==> false)
                    && a₆₇₃ < 100000
                    && cc₂₄[c₆₇₄] == aa₂₁[a₆₇₃]))
        && (forall c₆₇₇: int, a₆₇₆: int, b₆₇₈: int ::
                  0 <= c₆₇₇
                  && c₆₇₇ < c₂₃
                  && 0 <= a₆₇₆
                  && a₆₇₆ < a₂₅
                  && 0 <= b₆₇₈
                  && b₆₇₈ < b₂₆
                ||   bb₂₇[b₆₇₈] == bb[b₆₇₈]
                  && cc₂₄[c₆₇₇] == cc[c₆₇₇])
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₇₀₆: int, a₇₀₅: int, b₇₀₇: int ::
              (  0 <= c₇₀₆
                && c₇₀₆ < c₂₃
                && 0 <= a₇₀₅
                && a₇₀₅ < a₂₅
                && 0 <= b₇₀₇
                && b₇₀₇ < b₂₆
                 ==> 0 <= aa₂₁[a₇₀₅]
                    && a₇₀₅ < 100000
                    && bb₂₇[b₇₀₇] == aa₂₁[a₇₀₅]
                  ||   (0 <= aa₂₁[a₇₀₅]
                       ==> false)
                    && a₇₀₅ < 100000
                    && cc₂₄[c₇₀₆] == aa₂₁[a₇₀₅]))
        && (forall c₇₀₉: int, a₇₀₈: int, b₇₁₀: int ::
                  0 <= c₇₀₉
                  && c₇₀₉ < c₂₃
                  && 0 <= a₇₀₈
                  && a₇₀₈ < a₂₅
                  && 0 <= b₇₁₀
                  && b₇₁₀ < b₂₆
                ||   bb₂₇[b₇₁₀] == bb[b₇₁₀]
                  && cc₂₄[c₇₀₉] == cc[c₇₀₉])
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₇₈₂: int, a₇₈₁: int, b₁₀: int ::
              (  0 <= c₇₈₂
                && c₇₈₂ < c₂₃
                && 0 <= a₇₈₁
                && a₇₈₁ < a₂₅
                && 0 <= b₁₀
                && b₁₀ < b₂₆
                 ==> 0 <= aa₂₁[a₇₈₁]
                    && a₇₈₁ < 100000
                    && bb₂₇[b₁₀] == aa₂₁[a₇₈₁]
                  ||   (0 <= aa₂₁[a₇₈₁]
                       ==> false)
                    && a₇₈₁ < 100000
                    && cc₂₄[c₇₈₂] == aa₂₁[a₇₈₁]))
        && (forall c₇₈₄: int, a₇₈₃: int, b₁₀: int ::
                  0 <= c₇₈₄
                  && c₇₈₄ < c₂₃
                  && 0 <= a₇₈₃
                  && a₇₈₃ < a₂₅
                  && 0 <= b₁₀
                  && b₁₀ < b₂₆
                ||   bb₂₇[b₁₀] == bb[b₁₀]
                  && cc₂₄[c₇₈₄] == cc[c₇₈₄])
        && a₂₅ < 100000
         ==> 0 <= a₉
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₈₁₀: int, a₈₀₉: int, b₁₀: int ::
              (  0 <= c₈₁₀
                && c₈₁₀ < c₂₃
                && 0 <= a₈₀₉
                && a₈₀₉ < a₂₅
                && 0 <= b₁₀
                && b₁₀ < b₂₆
                 ==> 0 <= aa₂₁[a₈₀₉]
                    && a₈₀₉ < 100000
                    && bb₂₇[b₁₀] == aa₂₁[a₈₀₉]
                  ||   (0 <= aa₂₁[a₈₀₉]
                       ==> false)
                    && a₈₀₉ < 100000
                    && cc₂₄[c₈₁₀] == aa₂₁[a₈₀₉]))
        && (forall c₈₁₂: int, a₈₁₁: int, b₁₀: int ::
                  0 <= c₈₁₂
                  && c₈₁₂ < c₂₃
                  && 0 <= a₈₁₁
                  && a₈₁₁ < a₂₅
                  && 0 <= b₁₀
                  && b₁₀ < b₂₆
                ||   bb₂₇[b₁₀] == bb[b₁₀]
                  && cc₂₄[c₈₁₂] == cc[c₈₁₂])
        && a₂₅ < 100000
         ==> a₉ < a₂₅ + 1
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₈₃₆: int, a₉: int, b₈₃₇: int ::
              (  0 <= c₈₃₆
                && c₈₃₆ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₈₃₇
                && b₈₃₇ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₈₃₇] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₈₃₆] == aa₂₁[a₉]))
        && (forall c₈₃₈: int, a₉: int, b₈₃₉: int ::
                  0 <= c₈₃₈
                  && c₈₃₈ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₈₃₉
                  && b₈₃₉ < b₂₆
                ||   bb₂₇[b₈₃₉] == bb[b₈₃₉]
                  && cc₂₄[c₈₃₈] == cc[c₈₃₈])
        && a₂₅ < 100000
         ==> 0 <= b₁₀
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, b₁₀: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
        && (forall c₈₆₃: int, a₉: int, b₈₆₄: int ::
              (  0 <= c₈₆₃
                && c₈₆₃ < c₂₃
                && 0 <= a₉
                && a₉ < a₂₅
                && 0 <= b₈₆₄
                && b₈₆₄ < b₂₆
                 ==> 0 <= aa₂₁[a₉]
                    && a₉ < 100000
                    && bb₂₇[b₈₆₄] == aa₂₁[a₉]
                  ||   (0 <= aa₂₁[a₉]
                       ==> false)
                    && a₉ < 100000
                    && cc₂₄[c₈₆₃] == aa₂₁[a₉]))
        && (forall c₈₆₅: int, a₉: int, b₈₆₆: int ::
                  0 <= c₈₆₅
                  && c₈₆₅ < c₂₃
                  && 0 <= a₉
                  && a₉ < a₂₅
                  && 0 <= b₈₆₆
                  && b₈₆₆ < b₂₆
                ||   bb₂₇[b₈₆₆] == bb[b₈₆₆]
                  && cc₂₄[c₈₆₅] == cc[c₈₆₅])
        && a₂₅ < 100000
         ==> b₁₀ < b₂₆
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, x₂₈: int ::
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
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
        && x₂₈ <= b₂₆
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
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && a₂₅ <= 100000
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
        && x₂₈ <= b₂₆
        && (forall x₁₇: int ::
              (  0 <= x₁₇
                && x₁₇ < x₂₈
                 ==> x₁₇ < b₂₆))
        && 0 <= x₂₉
        && x₂₉ <= c₂₃
        && (forall x₁₉: int ::
              (  0 <= x₁₉
                && x₁₉ < x₂₉
                 ==> x₁₉ < c₂₃))
        && x₂₉ < c₂₃
         ==> x₂₈ < b₂₆
          || a₂₅ < 100000
          || i₂₂ < 100000
          || cc₂₄[x₂₉] < 0));

