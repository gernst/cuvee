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
        && (forall c₅₆₀: int, a₅₅₉: int, b₅₆₁: int ::
              (  c₅₆₀ + c₅₆₀ == a₅₅₉ + a₅₅₉
                && c₅₆₀ + c₅₆₀ == b₅₆₁ + b₅₆₁
                && 0 <= c₅₆₀
                && c₅₆₀ < c₂₃
                && 0 <= a₅₅₉
                && a₅₅₉ < a₂₅
                && 0 <= b₅₆₁
                && b₅₆₁ < b₂₆
                 ==> 0 <= aa₂₁[a₅₅₉]
                    && a₅₅₉ < 100000
                    && bb₂₇[b₅₆₁] == aa₂₁[a₅₅₉]
                  ||   (0 <= aa₂₁[a₅₅₉]
                       ==> false)
                    && a₅₅₉ < 100000
                    && cc₂₄[c₅₆₀] == aa₂₁[a₅₅₉]))
        && (forall c₅₆₃: int, a₅₆₂: int, b₅₆₄: int ::
              (  c₅₆₃ + c₅₆₃ == a₅₆₂ + a₅₆₂
                && c₅₆₃ + c₅₆₃ == b₅₆₄ + b₅₆₄
                 ==> 0 <= c₅₆₃
                    && c₅₆₃ < c₂₃
                    && 0 <= a₅₆₂
                    && a₅₆₂ < a₂₅
                    && 0 <= b₅₆₄
                    && b₅₆₄ < b₂₆
                  ||   bb₂₇[b₅₆₄] == bb[b₅₆₄]
                    && cc₂₄[c₅₆₃] == cc[c₅₆₃]))
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
        && (forall c₆₁₈: int, a₆₁₇: int, b₆₁₉: int ::
              (  c₆₁₈ + c₆₁₈ == a₆₁₇ + a₆₁₇
                && c₆₁₈ + c₆₁₈ == b₆₁₉ + b₆₁₉
                && 0 <= c₆₁₈
                && c₆₁₈ < c₂₃
                && 0 <= a₆₁₇
                && a₆₁₇ < a₂₅
                && 0 <= b₆₁₉
                && b₆₁₉ < b₂₆
                 ==> 0 <= aa₂₁[a₆₁₇]
                    && a₆₁₇ < 100000
                    && bb₂₇[b₆₁₉] == aa₂₁[a₆₁₇]
                  ||   (0 <= aa₂₁[a₆₁₇]
                       ==> false)
                    && a₆₁₇ < 100000
                    && cc₂₄[c₆₁₈] == aa₂₁[a₆₁₇]))
        && (forall c₆₂₁: int, a₆₂₀: int, b₆₂₂: int ::
              (  c₆₂₁ + c₆₂₁ == a₆₂₀ + a₆₂₀
                && c₆₂₁ + c₆₂₁ == b₆₂₂ + b₆₂₂
                 ==> 0 <= c₆₂₁
                    && c₆₂₁ < c₂₃
                    && 0 <= a₆₂₀
                    && a₆₂₀ < a₂₅
                    && 0 <= b₆₂₂
                    && b₆₂₂ < b₂₆
                  ||   bb₂₇[b₆₂₂] == bb[b₆₂₂]
                    && cc₂₄[c₆₂₁] == cc[c₆₂₁]))
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

