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
                        i₅ < 100000
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
                        i₅ < 100000
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
                        i₅ < 100000
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
        && (forall c₂₆₉: int, a₂₆₈: int, b₂₇₀: int ::
              (  c₂₆₉ + c₂₆₉ == a₂₆₈ + a₂₆₈
                && c₂₆₉ + c₂₆₉ == b₂₇₀ + b₂₇₀
                && 0 <= c₂₆₉
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
              (  c₂₇₂ + c₂₇₂ == a₂₇₁ + a₂₇₁
                && c₂₇₂ + c₂₇₂ == b₂₇₃ + b₂₇₃
                 ==> 0 <= c₂₇₂
                    && c₂₇₂ < c₂₃
                    && 0 <= a₂₇₁
                    && a₂₇₁ < a₂₅
                    && 0 <= b₂₇₃
                    && b₂₇₃ < b₂₆
                  ||   bb₂₇[b₂₇₃] == bb[b₂₇₃]
                    && cc₂₄[c₂₇₂] == cc[c₂₇₂]))
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
                        i₅ < 100000
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
                        i₅ < 100000
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
        && (forall c₆₁₁: int, a₆₁₀: int, b₆₁₂: int ::
              (  c₆₁₁ + c₆₁₁ == a₆₁₀ + a₆₁₀
                && c₆₁₁ + c₆₁₁ == b₆₁₂ + b₆₁₂
                && 0 <= c₆₁₁
                && c₆₁₁ < c₂₃
                && 0 <= a₆₁₀
                && a₆₁₀ < a₂₅
                && 0 <= b₆₁₂
                && b₆₁₂ < b₂₆
                 ==> 0 <= aa₂₁[a₆₁₀]
                    && a₆₁₀ < 100000
                    && bb₂₇[b₆₁₂] == aa₂₁[a₆₁₀]
                  ||   (0 <= aa₂₁[a₆₁₀]
                       ==> false)
                    && a₆₁₀ < 100000
                    && cc₂₄[c₆₁₁] == aa₂₁[a₆₁₀]))
        && (forall c₆₁₄: int, a₆₁₃: int, b₆₁₅: int ::
              (  c₆₁₄ + c₆₁₄ == a₆₁₃ + a₆₁₃
                && c₆₁₄ + c₆₁₄ == b₆₁₅ + b₆₁₅
                 ==> 0 <= c₆₁₄
                    && c₆₁₄ < c₂₃
                    && 0 <= a₆₁₃
                    && a₆₁₃ < a₂₅
                    && 0 <= b₆₁₅
                    && b₆₁₅ < b₂₆
                  ||   bb₂₇[b₆₁₅] == bb[b₆₁₅]
                    && cc₂₄[c₆₁₄] == cc[c₆₁₄]))
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
                        i₅ < 100000
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
                        i₅ < 100000
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

