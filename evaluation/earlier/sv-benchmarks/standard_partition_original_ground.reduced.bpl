data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int ::
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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₉: int, b₁₀: int ::
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                && 0 <= c₈
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
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                 ==> 0 <= c₈
                    && c₈ < c₂₃
                    && 0 <= a₉
                    && a₉ < a₂₅
                    && 0 <= b₁₀
                    && b₁₀ < b₂₆
                  ||   bb₂₇[b₁₀] == bb[b₁₀]
                    && cc₂₄[c₈] == cc[c₈]))
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> i₂₂ < 100000
          || c₂₃ + 0 == 0 + a₂₅ + 1));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int ::
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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₉: int, b₁₀: int ::
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                && 0 <= c₈
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
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                 ==> 0 <= c₈
                    && c₈ < c₂₃
                    && 0 <= a₉
                    && a₉ < a₂₅
                    && 0 <= b₁₀
                    && b₁₀ < b₂₆
                  ||   bb₂₇[b₁₀] == bb[b₁₀]
                    && cc₂₄[c₈] == cc[c₈]))
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
         ==> i₂₂ < 100000
          || c₂₃ + 0 == 0 + b₂₆ + 1));

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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₃₉₉: int, a₃₉₈: int, b₄₀₀: int ::
              (  c₃₉₉ + c₃₉₉ == a₃₉₈ + a₃₉₈
                && c₃₉₉ + c₃₉₉ == b₄₀₀ + b₄₀₀
                && 0 <= c₃₉₉
                && c₃₉₉ < c₂₃
                && 0 <= a₃₉₈
                && a₃₉₈ < a₂₅
                && 0 <= b₄₀₀
                && b₄₀₀ < b₂₆
                 ==> 0 <= aa₂₁[a₃₉₈]
                    && a₃₉₈ < 100000
                    && bb₂₇[b₄₀₀] == aa₂₁[a₃₉₈]
                  ||   (0 <= aa₂₁[a₃₉₈]
                       ==> false)
                    && a₃₉₈ < 100000
                    && cc₂₄[c₃₉₉] == aa₂₁[a₃₉₈]))
        && (forall c₄₀₂: int, a₄₀₁: int, b₄₀₃: int ::
              (  c₄₀₂ + c₄₀₂ == a₄₀₁ + a₄₀₁
                && c₄₀₂ + c₄₀₂ == b₄₀₃ + b₄₀₃
                 ==> 0 <= c₄₀₂
                    && c₄₀₂ < c₂₃
                    && 0 <= a₄₀₁
                    && a₄₀₁ < a₂₅
                    && 0 <= b₄₀₃
                    && b₄₀₃ < b₂₆
                  ||   bb₂₇[b₄₀₃] == bb[b₄₀₃]
                    && cc₂₄[c₄₀₂] == cc[c₄₀₂]))
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> 0 <= c₈
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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₄₃₁: int, a₄₃₀: int, b₄₃₂: int ::
              (  c₄₃₁ + c₄₃₁ == a₄₃₀ + a₄₃₀
                && c₄₃₁ + c₄₃₁ == b₄₃₂ + b₄₃₂
                && 0 <= c₄₃₁
                && c₄₃₁ < c₂₃
                && 0 <= a₄₃₀
                && a₄₃₀ < a₂₅
                && 0 <= b₄₃₂
                && b₄₃₂ < b₂₆
                 ==> 0 <= aa₂₁[a₄₃₀]
                    && a₄₃₀ < 100000
                    && bb₂₇[b₄₃₂] == aa₂₁[a₄₃₀]
                  ||   (0 <= aa₂₁[a₄₃₀]
                       ==> false)
                    && a₄₃₀ < 100000
                    && cc₂₄[c₄₃₁] == aa₂₁[a₄₃₀]))
        && (forall c₄₃₄: int, a₄₃₃: int, b₄₃₅: int ::
              (  c₄₃₄ + c₄₃₄ == a₄₃₃ + a₄₃₃
                && c₄₃₄ + c₄₃₄ == b₄₃₅ + b₄₃₅
                 ==> 0 <= c₄₃₄
                    && c₄₃₄ < c₂₃
                    && 0 <= a₄₃₃
                    && a₄₃₃ < a₂₅
                    && 0 <= b₄₃₅
                    && b₄₃₅ < b₂₆
                  ||   bb₂₇[b₄₃₅] == bb[b₄₃₅]
                    && cc₂₄[c₄₃₄] == cc[c₄₃₄]))
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> c₈ < c₂₃
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int ::
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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₉: int, b₁₀: int ::
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                && 0 <= c₈
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
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                 ==> 0 <= c₈
                    && c₈ < c₂₃
                    && 0 <= a₉
                    && a₉ < a₂₅
                    && 0 <= b₁₀
                    && b₁₀ < b₂₆
                  ||   bb₂₇[b₁₀] == bb[b₁₀]
                    && cc₂₄[c₈] == cc[c₈]))
        && a₂₅ < 100000
         ==> 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || c₂₃ + 1 + 0 == 0 + b₂₆));

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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈₂₅: int, a₈₂₄: int, b₈₂₆: int ::
              (  c₈₂₅ + c₈₂₅ == a₈₂₄ + a₈₂₄
                && c₈₂₅ + c₈₂₅ == b₈₂₆ + b₈₂₆
                && 0 <= c₈₂₅
                && c₈₂₅ < c₂₃
                && 0 <= a₈₂₄
                && a₈₂₄ < a₂₅
                && 0 <= b₈₂₆
                && b₈₂₆ < b₂₆
                 ==> 0 <= aa₂₁[a₈₂₄]
                    && a₈₂₄ < 100000
                    && bb₂₇[b₈₂₆] == aa₂₁[a₈₂₄]
                  ||   (0 <= aa₂₁[a₈₂₄]
                       ==> false)
                    && a₈₂₄ < 100000
                    && cc₂₄[c₈₂₅] == aa₂₁[a₈₂₄]))
        && (forall c₈₂₈: int, a₈₂₇: int, b₈₂₉: int ::
              (  c₈₂₈ + c₈₂₈ == a₈₂₇ + a₈₂₇
                && c₈₂₈ + c₈₂₈ == b₈₂₉ + b₈₂₉
                 ==> 0 <= c₈₂₈
                    && c₈₂₈ < c₂₃
                    && 0 <= a₈₂₇
                    && a₈₂₇ < a₂₅
                    && 0 <= b₈₂₉
                    && b₈₂₉ < b₂₆
                  ||   bb₂₇[b₈₂₉] == bb[b₈₂₉]
                    && cc₂₄[c₈₂₈] == cc[c₈₂₈]))
        && a₂₅ < 100000
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> a₉ < a₂₅ + 1
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈₈₃: int, a₈₈₂: int, b₈₈₄: int ::
              (  c₈₈₃ + c₈₈₃ == a₈₈₂ + a₈₈₂
                && c₈₈₃ + c₈₈₃ == b₈₈₄ + b₈₈₄
                && 0 <= c₈₈₃
                && c₈₈₃ < c₂₃
                && 0 <= a₈₈₂
                && a₈₈₂ < a₂₅
                && 0 <= b₈₈₄
                && b₈₈₄ < b₂₆
                 ==> 0 <= aa₂₁[a₈₈₂]
                    && a₈₈₂ < 100000
                    && bb₂₇[b₈₈₄] == aa₂₁[a₈₈₂]
                  ||   (0 <= aa₂₁[a₈₈₂]
                       ==> false)
                    && a₈₈₂ < 100000
                    && cc₂₄[c₈₈₃] == aa₂₁[a₈₈₂]))
        && (forall c₈₈₆: int, a₈₈₅: int, b₈₈₇: int ::
              (  c₈₈₆ + c₈₈₆ == a₈₈₅ + a₈₈₅
                && c₈₈₆ + c₈₈₆ == b₈₈₇ + b₈₈₇
                 ==> 0 <= c₈₈₆
                    && c₈₈₆ < c₂₃
                    && 0 <= a₈₈₅
                    && a₈₈₅ < a₂₅
                    && 0 <= b₈₈₇
                    && b₈₈₇ < b₂₆
                  ||   bb₂₇[b₈₈₇] == bb[b₈₈₇]
                    && cc₂₄[c₈₈₆] == cc[c₈₈₆]))
        && a₂₅ < 100000
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₉: int, b₁₀: int ::
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                && 0 <= c₈
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
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                 ==> 0 <= c₈
                    && c₈ < c₂₃
                    && 0 <= a₉
                    && a₉ < a₂₅
                    && 0 <= b₁₀
                    && b₁₀ < b₂₆
                  ||   bb₂₇[b₁₀] == bb[b₁₀]
                    && cc₂₄[c₈] == cc[c₈]))
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
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₈: int, a₉: int, b₁₀: int ::
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                && 0 <= c₈
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
              (  c₈ + c₈ == a₉ + a₉
                && c₈ + c₈ == b₁₀ + b₁₀
                 ==> 0 <= c₈
                    && c₈ < c₂₃
                    && 0 <= a₉
                    && a₉ < a₂₅
                    && 0 <= b₁₀
                    && b₁₀ < b₂₆
                  ||   bb₂₇[b₁₀] == bb[b₁₀]
                    && cc₂₄[c₈] == cc[c₈]))
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

