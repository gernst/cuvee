data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₃₁: int, a: [int]int, a₃₂: [int]int, i₃₃: int, i₃₅: int, i₃₇: int, i₃₉: int, i₄₁: int, i₄₃: int, sum₄₄: int, i₄₅: int ::
      (  -2147483648 <= SIZE₃₁
        && SIZE₃₁ < 2147483648
        && 1 < SIZE₃₁
        && SIZE₃₁ < 100000
        && 0 <= i₃₃
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₃₃
                 ==> i₄ < SIZE₃₁
                  && a₃₂[i₄] == 1))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₃₃
                || a₃₂[i₄] == a[i₄])
        && 0 <= i₃₅
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₃₅
                 ==> i₈ < SIZE₃₁))
        && 0 <= i₃₇
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₃₇
                 ==> i₁₂ < SIZE₃₁))
        && 0 <= i₃₉
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₃₉
                 ==> i₁₆ < SIZE₃₁))
        && 0 <= i₄₁
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₄₁
                 ==> i₂₀ < SIZE₃₁))
        && 0 <= i₄₃
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₄₃
                 ==> i₂₄ < SIZE₃₁))
        && 0 <= i₄₅
        && (forall i₂₈: int ::
              (  0 <= i₂₈
                && i₂₈ < i₄₅
                 ==> i₂₈ < SIZE₃₁))
         ==> i₄₅ < SIZE₃₁
          || i₄₃ < SIZE₃₁
          || i₄₁ < SIZE₃₁
          || i₃₉ < SIZE₃₁
          || i₃₇ < SIZE₃₁
          || i₃₅ < SIZE₃₁
          || i₃₃ < SIZE₃₁
          || sum₄₄ == 0));

