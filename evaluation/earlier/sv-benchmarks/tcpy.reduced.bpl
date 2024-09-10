data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall SIZE₁₄: int, a: [int]int, acopy: [int]int, a₁₅: [int]int, i₁₆: int, acopy₁₇: [int]int, i₁₈: int, i₉: int ::
      (  -2147483648 <= SIZE₁₄
        && SIZE₁₄ < 2147483648
        && 1 < SIZE₁₄
        && SIZE₁₄ < 100000
        && 0 <= i₁₆
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₆
                 ==> (exists nondet_int₁₅: int ::
                        -2147483648 <= nondet_int₁₅
                        && nondet_int₁₅ < 2147483648
                        && i₆ < SIZE₁₄
                        && a₁₅[i₆] == nondet_int₁₅)))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₆
                || a₁₅[i₆] == a[i₆])
        && SIZE₁₄ % 2 == 0
        && SIZE₁₄ % 2 == 0
        && 0 <= i₁₈
        && (forall i₁₅₈: int ::
              (  0 <= i₁₅₈
                && i₁₅₈ < i₁₈
                 ==> i₁₅₈ < SIZE₁₄ / 2
                  && acopy₁₇[i₁₅₈] == a₁₅[i₁₅₈]
                  &&   -1 + SIZE₁₄ + -i₁₅₈ == i₁₅₈
                    || acopy₁₇[-1 + SIZE₁₄ + -i₁₅₈] == a₁₅[-1 + SIZE₁₄ + -i₁₅₈]))
        && (forall i₁₅₉: int ::
                  0 <= i₁₅₉
                  && i₁₅₉ < i₁₈
                ||   acopy₁₇[i₁₅₉] == acopy[i₁₅₉]
                  && acopy₁₇[-1 + SIZE₁₄ + -i₁₅₉] == acopy[-1 + SIZE₁₄ + -i₁₅₉])
        && i₁₈ < SIZE₁₄ / 2
         ==> i₉ < i₁₈ + 1
          || i₁₆ < SIZE₁₄
          || acopy₁₇[SIZE₁₄ - i₁₈ - 1 := a₁₅[SIZE₁₄ - i₁₈ - 1]][i₁₈ := a₁₅[i₁₈]][i₉] == acopy[i₉]));

goal {:named "invariant forward"} (forall SIZE₁₄: int, a: [int]int, acopy: [int]int, a₁₅: [int]int, i₁₆: int, acopy₁₇: [int]int, i₁₈: int, i₉: int ::
      (  -2147483648 <= SIZE₁₄
        && SIZE₁₄ < 2147483648
        && 1 < SIZE₁₄
        && SIZE₁₄ < 100000
        && 0 <= i₁₆
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₆
                 ==> (exists nondet_int₁₅: int ::
                        -2147483648 <= nondet_int₁₅
                        && nondet_int₁₅ < 2147483648
                        && i₆ < SIZE₁₄
                        && a₁₅[i₆] == nondet_int₁₅)))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₆
                || a₁₅[i₆] == a[i₆])
        && SIZE₁₄ % 2 == 0
        && SIZE₁₄ % 2 == 0
        && 0 <= i₁₈
        && (forall i₁₆₈: int ::
              (  0 <= i₁₆₈
                && i₁₆₈ < i₁₈
                 ==> i₁₆₈ < SIZE₁₄ / 2
                  && acopy₁₇[i₁₆₈] == a₁₅[i₁₆₈]
                  &&   -1 + SIZE₁₄ + -i₁₆₈ == i₁₆₈
                    || acopy₁₇[-1 + SIZE₁₄ + -i₁₆₈] == a₁₅[-1 + SIZE₁₄ + -i₁₆₈]))
        && (forall i₁₆₉: int ::
                  0 <= i₁₆₉
                  && i₁₆₉ < i₁₈
                ||   acopy₁₇[i₁₆₉] == acopy[i₁₆₉]
                  && acopy₁₇[-1 + SIZE₁₄ + -i₁₆₉] == acopy[-1 + SIZE₁₄ + -i₁₆₉])
        && i₁₈ < SIZE₁₄ / 2
         ==> i₉ < i₁₈ + 1
          || i₁₆ < SIZE₁₄
          || acopy₁₇[SIZE₁₄ - i₁₈ - 1 := a₁₅[SIZE₁₄ - i₁₈ - 1]][i₁₈ := a₁₅[i₁₈]][-1 + SIZE₁₄ + -i₉] == acopy[-1 + SIZE₁₄ + -i₉]));

