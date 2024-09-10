data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall a: [int]int, a₁₃: [int]int, j₁₄: int, i₁₆: int, x: int, j₄: int, i₆: int ::
      (  0 <= i₁₆
        && (forall j₇₁: int, i₇₂: int ::
              (  0 <= i₇₂
                && i₇₂ < i₁₆
                 ==> (exists x₃: int ::
                        x₃ == 0
                        && -2147483648 <= x₃
                        && x₃ < 2147483648
                        && i₇₂ < 100000
                        && a₁₃[i₇₂] == j₇₁)))
        && (forall i₇₃: int ::
                  0 <= i₇₃
                  && i₇₃ < i₁₆
                || a₁₃[i₇₃] == a[i₇₃])
        && (forall i₇₄: int, x₃: int ::
              (  0 <= i₇₄
                && i₇₄ < i₁₆
                && -2147483648 <= x₃
                && x₃ < 2147483648
                && i₇₄ < 100000
                 ==> x₃ == 0))
        && i₁₆ < 100000
        && -2147483648 <= x
        && x < 2147483648
        && x == 0
        && 0 <= i₆
        && i₆ < i₁₆ + 1
         ==> (exists x₃: int ::
                x₃ == 0
                && -2147483648 <= x₃
                && x₃ < 2147483648
                && i₆ < 100000
                && a₁₃[i₁₆ := j₁₄][i₆] == j₄)));

goal {:named "invariant forward"} (forall a: [int]int, a₁₃: [int]int, i₁₆: int, x: int, i₆: int, x₃: int ::
      (  0 <= i₁₆
        && (forall j₄: int, i₉₃: int ::
              (  0 <= i₉₃
                && i₉₃ < i₁₆
                 ==> (exists x₉₄: int ::
                        x₉₄ == 0
                        && -2147483648 <= x₉₄
                        && x₉₄ < 2147483648
                        && i₉₃ < 100000
                        && a₁₃[i₉₃] == j₄)))
        && (forall i₉₅: int ::
                  0 <= i₉₅
                  && i₉₅ < i₁₆
                || a₁₃[i₉₅] == a[i₉₅])
        && (forall i₉₇: int, x₉₆: int ::
              (  0 <= i₉₇
                && i₉₇ < i₁₆
                && -2147483648 <= x₉₆
                && x₉₆ < 2147483648
                && i₉₇ < 100000
                 ==> x₉₆ == 0))
        && i₁₆ < 100000
        && -2147483648 <= x
        && x < 2147483648
        && x == 0
        && 0 <= i₆
        && i₆ < i₁₆ + 1
        && -2147483648 <= x₃
        && x₃ < 2147483648
        && i₆ < 100000
         ==> x₃ == 0));

