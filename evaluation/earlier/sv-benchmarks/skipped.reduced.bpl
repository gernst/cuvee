data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  -2147483648 <= SIZE₁₃
        && SIZE₁₃ < 2147483648
        && 1 < SIZE₁₃
        && SIZE₁₃ < 100000
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < SIZE₁₃
                        && a₁₄[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                || a₁₄[i₅] == a[i₅])
        && SIZE₁₃ % 2 == 0
        && SIZE₁₃ % 2 == 0
        && 1 <= i₁₇
        && (forall i₈: int ::
              (  1 <= i₈
                && i₈ < i₁₇
                 ==> -1 + 2 * i₈ < a₁₆[-2 + 2 * i₈ := -2 + 2 * i₈][-1 + 2 * i₈]
                    && -2 + 2 * i₈ < a₁₆[-2 + 2 * i₈]
                    && i₈ <= SIZE₁₃ / 2
                    && a₁₆[-1 + 2 * i₈] == -1 + 2 * i₈
                    &&   -2 + 2 * i₈ == -1 + 2 * i₈
                      || a₁₆[-2 + 2 * i₈] == -2 + 2 * i₈
                  ||   -1 + 2 * i₈ < a₁₆[-1 + 2 * i₈]
                    && (-2 + 2 * i₈ < a₁₆[-2 + 2 * i₈]
                       ==> false)
                    && i₈ <= SIZE₁₃ / 2
                    && a₁₆[-1 + 2 * i₈] == -1 + 2 * i₈
                  ||   (-1 + 2 * i₈ < a₁₆[-2 + 2 * i₈ := -2 + 2 * i₈][-1 + 2 * i₈]
                       ==> false)
                    && -2 + 2 * i₈ < a₁₆[-2 + 2 * i₈]
                    && i₈ <= SIZE₁₃ / 2
                    && a₁₆[-2 + 2 * i₈] == -2 + 2 * i₈
                  ||   (-1 + 2 * i₈ < a₁₆[-1 + 2 * i₈]
                       ==> false)
                    && (-2 + 2 * i₈ < a₁₆[-2 + 2 * i₈]
                       ==> false)
                    && i₈ <= SIZE₁₃ / 2))
        && (forall i₈: int ::
                  1 <= i₈
                  && i₈ < i₁₇
                ||   a₁₆[-1 + 2 * i₈] == a₁₄[-1 + 2 * i₈]
                  && a₁₆[-2 + 2 * i₈] == a₁₄[-2 + 2 * i₈])
        && 0 <= i₁₈
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₁₈
                 ==> i₁₁ < SIZE₁₃))
        && i₁₈ < SIZE₁₃
         ==> i₁₇ <= SIZE₁₃ / 2
          || i₁₅ < SIZE₁₃
          || a₁₆[i₁₈] <= i₁₈));

