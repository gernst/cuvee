data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
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

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
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

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₂₇₀: int, a₂₆₉: int, b₂₇₁: int ::
              (  c₂₇₀ + c₂₇₀ == a₂₆₉ + a₂₆₉
                && c₂₇₀ + c₂₇₀ == b₂₇₁ + b₂₇₁
                && 0 <= c₂₇₀
                && c₂₇₀ < c₂₃
                && 0 <= a₂₆₉
                && a₂₆₉ < a₂₅
                && 0 <= b₂₇₁
                && b₂₇₁ < b₂₆
                 ==> 0 <= aa₂₁[a₂₆₉]
                    && a₂₆₉ < 100000
                    && bb₂₇[b₂₇₁] == aa₂₁[a₂₆₉]
                  ||   (0 <= aa₂₁[a₂₆₉]
                       ==> false)
                    && a₂₆₉ < 100000
                    && cc₂₄[c₂₇₀] == aa₂₁[a₂₆₉]))
        && (forall c₂₇₃: int, a₂₇₂: int, b₂₇₄: int ::
              (  c₂₇₃ + c₂₇₃ == a₂₇₂ + a₂₇₂
                && c₂₇₃ + c₂₇₃ == b₂₇₄ + b₂₇₄
                 ==> 0 <= c₂₇₃
                    && c₂₇₃ < c₂₃
                    && 0 <= a₂₇₂
                    && a₂₇₂ < a₂₅
                    && 0 <= b₂₇₄
                    && b₂₇₄ < b₂₆
                  ||   bb₂₇[b₂₇₄] == bb[b₂₇₄]
                    && cc₂₄[c₂₇₃] == cc[c₂₇₃]))
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> c₈ < c₂₃
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₃₀₂: int, a₃₀₁: int, b₃₀₃: int ::
              (  c₃₀₂ + c₃₀₂ == a₃₀₁ + a₃₀₁
                && c₃₀₂ + c₃₀₂ == b₃₀₃ + b₃₀₃
                && 0 <= c₃₀₂
                && c₃₀₂ < c₂₃
                && 0 <= a₃₀₁
                && a₃₀₁ < a₂₅
                && 0 <= b₃₀₃
                && b₃₀₃ < b₂₆
                 ==> 0 <= aa₂₁[a₃₀₁]
                    && a₃₀₁ < 100000
                    && bb₂₇[b₃₀₃] == aa₂₁[a₃₀₁]
                  ||   (0 <= aa₂₁[a₃₀₁]
                       ==> false)
                    && a₃₀₁ < 100000
                    && cc₂₄[c₃₀₂] == aa₂₁[a₃₀₁]))
        && (forall c₃₀₅: int, a₃₀₄: int, b₃₀₆: int ::
              (  c₃₀₅ + c₃₀₅ == a₃₀₄ + a₃₀₄
                && c₃₀₅ + c₃₀₅ == b₃₀₆ + b₃₀₆
                 ==> 0 <= c₃₀₅
                    && c₃₀₅ < c₂₃
                    && 0 <= a₃₀₄
                    && a₃₀₄ < a₂₅
                    && 0 <= b₃₀₆
                    && b₃₀₆ < b₂₆
                  ||   bb₂₇[b₃₀₆] == bb[b₃₀₆]
                    && cc₂₄[c₃₀₅] == cc[c₃₀₅]))
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> 0 <= a₉
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₃₃₄: int, a₃₃₃: int, b₃₃₅: int ::
              (  c₃₃₄ + c₃₃₄ == a₃₃₃ + a₃₃₃
                && c₃₃₄ + c₃₃₄ == b₃₃₅ + b₃₃₅
                && 0 <= c₃₃₄
                && c₃₃₄ < c₂₃
                && 0 <= a₃₃₃
                && a₃₃₃ < a₂₅
                && 0 <= b₃₃₅
                && b₃₃₅ < b₂₆
                 ==> 0 <= aa₂₁[a₃₃₃]
                    && a₃₃₃ < 100000
                    && bb₂₇[b₃₃₅] == aa₂₁[a₃₃₃]
                  ||   (0 <= aa₂₁[a₃₃₃]
                       ==> false)
                    && a₃₃₃ < 100000
                    && cc₂₄[c₃₃₄] == aa₂₁[a₃₃₃]))
        && (forall c₃₃₇: int, a₃₃₆: int, b₃₃₈: int ::
              (  c₃₃₇ + c₃₃₇ == a₃₃₆ + a₃₃₆
                && c₃₃₇ + c₃₃₇ == b₃₃₈ + b₃₃₈
                 ==> 0 <= c₃₃₇
                    && c₃₃₇ < c₂₃
                    && 0 <= a₃₃₆
                    && a₃₃₆ < a₂₅
                    && 0 <= b₃₃₈
                    && b₃₃₈ < b₂₆
                  ||   bb₂₇[b₃₃₈] == bb[b₃₃₈]
                    && cc₂₄[c₃₃₇] == cc[c₃₃₇]))
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> a₉ < a₂₅ + 1
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₃₉₂: int, a₃₉₁: int, b₃₉₃: int ::
              (  c₃₉₂ + c₃₉₂ == a₃₉₁ + a₃₉₁
                && c₃₉₂ + c₃₉₂ == b₃₉₃ + b₃₉₃
                && 0 <= c₃₉₂
                && c₃₉₂ < c₂₃
                && 0 <= a₃₉₁
                && a₃₉₁ < a₂₅
                && 0 <= b₃₉₃
                && b₃₉₃ < b₂₆
                 ==> 0 <= aa₂₁[a₃₉₁]
                    && a₃₉₁ < 100000
                    && bb₂₇[b₃₉₃] == aa₂₁[a₃₉₁]
                  ||   (0 <= aa₂₁[a₃₉₁]
                       ==> false)
                    && a₃₉₁ < 100000
                    && cc₂₄[c₃₉₂] == aa₂₁[a₃₉₁]))
        && (forall c₃₉₅: int, a₃₉₄: int, b₃₉₆: int ::
              (  c₃₉₅ + c₃₉₅ == a₃₉₄ + a₃₉₄
                && c₃₉₅ + c₃₉₅ == b₃₉₆ + b₃₉₆
                 ==> 0 <= c₃₉₅
                    && c₃₉₅ < c₂₃
                    && 0 <= a₃₉₄
                    && a₃₉₄ < a₂₅
                    && 0 <= b₃₉₆
                    && b₃₉₆ < b₂₆
                  ||   bb₂₇[b₃₉₆] == bb[b₃₉₆]
                    && cc₂₄[c₃₉₅] == cc[c₃₉₅]))
        && a₂₅ < 100000
        && 0 <= aa₂₁[a₂₅]
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> b₁₀ < b₂₆ + 1
          || i₂₂ < 100000
          || bb₂₇[b₂₆ := aa₂₁[a₂₅]][b₁₀] == bb[b₁₀]));

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
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

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₅₇₈: int, a₅₇₇: int, b₅₇₉: int ::
              (  c₅₇₈ + c₅₇₈ == a₅₇₇ + a₅₇₇
                && c₅₇₈ + c₅₇₈ == b₅₇₉ + b₅₇₉
                && 0 <= c₅₇₈
                && c₅₇₈ < c₂₃
                && 0 <= a₅₇₇
                && a₅₇₇ < a₂₅
                && 0 <= b₅₇₉
                && b₅₇₉ < b₂₆
                 ==> 0 <= aa₂₁[a₅₇₇]
                    && a₅₇₇ < 100000
                    && bb₂₇[b₅₇₉] == aa₂₁[a₅₇₇]
                  ||   (0 <= aa₂₁[a₅₇₇]
                       ==> false)
                    && a₅₇₇ < 100000
                    && cc₂₄[c₅₇₈] == aa₂₁[a₅₇₇]))
        && (forall c₅₈₁: int, a₅₈₀: int, b₅₈₂: int ::
              (  c₅₈₁ + c₅₈₁ == a₅₈₀ + a₅₈₀
                && c₅₈₁ + c₅₈₁ == b₅₈₂ + b₅₈₂
                 ==> 0 <= c₅₈₁
                    && c₅₈₁ < c₂₃
                    && 0 <= a₅₈₀
                    && a₅₈₀ < a₂₅
                    && 0 <= b₅₈₂
                    && b₅₈₂ < b₂₆
                  ||   bb₂₇[b₅₈₂] == bb[b₅₈₂]
                    && cc₂₄[c₅₈₁] == cc[c₅₈₁]))
        && a₂₅ < 100000
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> a₉ < a₂₅ + 1
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal {:named "invariant forward"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, c₈: int, a₉: int, b₁₀: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || aa₂₁[i₅] == aa[i₅])
        && c₂₃ + 0 == 0 + a₂₅
        && c₂₃ + 0 == 0 + b₂₆
        && 0 <= c₂₃
        && 0 <= a₂₅
        && 0 <= b₂₆
        && (forall c₆₃₆: int, a₆₃₅: int, b₆₃₇: int ::
              (  c₆₃₆ + c₆₃₆ == a₆₃₅ + a₆₃₅
                && c₆₃₆ + c₆₃₆ == b₆₃₇ + b₆₃₇
                && 0 <= c₆₃₆
                && c₆₃₆ < c₂₃
                && 0 <= a₆₃₅
                && a₆₃₅ < a₂₅
                && 0 <= b₆₃₇
                && b₆₃₇ < b₂₆
                 ==> 0 <= aa₂₁[a₆₃₅]
                    && a₆₃₅ < 100000
                    && bb₂₇[b₆₃₇] == aa₂₁[a₆₃₅]
                  ||   (0 <= aa₂₁[a₆₃₅]
                       ==> false)
                    && a₆₃₅ < 100000
                    && cc₂₄[c₆₃₆] == aa₂₁[a₆₃₅]))
        && (forall c₆₃₉: int, a₆₃₈: int, b₆₄₀: int ::
              (  c₆₃₉ + c₆₃₉ == a₆₃₈ + a₆₃₈
                && c₆₃₉ + c₆₃₉ == b₆₄₀ + b₆₄₀
                 ==> 0 <= c₆₃₉
                    && c₆₃₉ < c₂₃
                    && 0 <= a₆₃₈
                    && a₆₃₈ < a₂₅
                    && 0 <= b₆₄₀
                    && b₆₄₀ < b₂₆
                  ||   bb₂₇[b₆₄₀] == bb[b₆₄₀]
                    && cc₂₄[c₆₃₉] == cc[c₆₃₉]))
        && a₂₅ < 100000
        && c₈ + c₈ == a₉ + a₉
        && c₈ + c₈ == b₁₀ + b₁₀
         ==> b₁₀ < b₂₆
          || 0 <= aa₂₁[a₂₅]
          || i₂₂ < 100000
          || cc₂₄[c₂₃ := aa₂₁[a₂₅]][c₈] == cc[c₈]));

goal {:named "assert"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, x₂₈: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
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

goal {:named "assert"} (forall aa: [int]int, bb: [int]int, cc: [int]int, aa₂₁: [int]int, i₂₂: int, c₂₃: int, cc₂₄: [int]int, a₂₅: int, b₂₆: int, bb₂₇: [int]int, x₂₈: int, x₂₉: int ::
      (  0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && aa₂₁[i₅] == nondet_int₁₄)))
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

