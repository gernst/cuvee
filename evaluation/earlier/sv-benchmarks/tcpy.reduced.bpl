data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall SIZE₁₄: int, a: [int]int, acopy: [int]int, a₁₅: [int]int, i₁₆: int, acopy₁₇: [int]int, i₁₈: int, i₉: int ::
      (  1 < SIZE₁₄
        && SIZE₁₄ < 100000
        && 0 <= i₁₆
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₆
                 ==> (exists nondet_int₁₅: int ::
                        i₆ < SIZE₁₄
                        && a₁₅[i₆] == nondet_int₁₅)))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₆
                || a₁₅[i₆] == a[i₆])
        && SIZE₁₄ % 2 == 0
        && SIZE₁₄ % 2 == 0
        && 0 <= i₁₈
        && (forall i₁₅₇: int ::
              (  0 <= i₁₅₇
                && i₁₅₇ < i₁₈
                 ==> i₁₅₇ < SIZE₁₄ / 2
                  && acopy₁₇[i₁₅₇] == a₁₅[i₁₅₇]
                  &&   -1 + SIZE₁₄ + -i₁₅₇ == i₁₅₇
                    || acopy₁₇[-1 + SIZE₁₄ + -i₁₅₇] == a₁₅[-1 + SIZE₁₄ + -i₁₅₇]))
        && (forall i₁₅₈: int ::
                  0 <= i₁₅₈
                  && i₁₅₈ < i₁₈
                ||   acopy₁₇[i₁₅₈] == acopy[i₁₅₈]
                  && acopy₁₇[-1 + SIZE₁₄ + -i₁₅₈] == acopy[-1 + SIZE₁₄ + -i₁₅₈])
        && i₁₈ < SIZE₁₄ / 2
         ==> i₉ < i₁₈ + 1
          || i₁₆ < SIZE₁₄
          || acopy₁₇[SIZE₁₄ - i₁₈ - 1 := a₁₅[SIZE₁₄ - i₁₈ - 1]][i₁₈ := a₁₅[i₁₈]][i₉] == acopy[i₉]));

goal {:named "invariant forward"} (forall SIZE₁₄: int, a: [int]int, acopy: [int]int, a₁₅: [int]int, i₁₆: int, acopy₁₇: [int]int, i₁₈: int, i₉: int ::
      (  1 < SIZE₁₄
        && SIZE₁₄ < 100000
        && 0 <= i₁₆
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₆
                 ==> (exists nondet_int₁₅: int ::
                        i₆ < SIZE₁₄
                        && a₁₅[i₆] == nondet_int₁₅)))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₆
                || a₁₅[i₆] == a[i₆])
        && SIZE₁₄ % 2 == 0
        && SIZE₁₄ % 2 == 0
        && 0 <= i₁₈
        && (forall i₁₆₇: int ::
              (  0 <= i₁₆₇
                && i₁₆₇ < i₁₈
                 ==> i₁₆₇ < SIZE₁₄ / 2
                  && acopy₁₇[i₁₆₇] == a₁₅[i₁₆₇]
                  &&   -1 + SIZE₁₄ + -i₁₆₇ == i₁₆₇
                    || acopy₁₇[-1 + SIZE₁₄ + -i₁₆₇] == a₁₅[-1 + SIZE₁₄ + -i₁₆₇]))
        && (forall i₁₆₈: int ::
                  0 <= i₁₆₈
                  && i₁₆₈ < i₁₈
                ||   acopy₁₇[i₁₆₈] == acopy[i₁₆₈]
                  && acopy₁₇[-1 + SIZE₁₄ + -i₁₆₈] == acopy[-1 + SIZE₁₄ + -i₁₆₈])
        && i₁₈ < SIZE₁₄ / 2
         ==> i₉ < i₁₈ + 1
          || i₁₆ < SIZE₁₄
          || acopy₁₇[SIZE₁₄ - i₁₈ - 1 := a₁₅[SIZE₁₄ - i₁₈ - 1]][i₁₈ := a₁₅[i₁₈]][-1 + SIZE₁₄ + -i₉] == acopy[-1 + SIZE₁₄ + -i₉]));

