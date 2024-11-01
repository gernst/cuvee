data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₁₅: int, a: [int]int, a₁₆: [int]int, i₁₇: int, i₁₉: int, sum₂₀: int, i₂₁: int ::
      (  1 < SIZE₁₅
        && SIZE₁₅ < 100000
        && 0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> i₄ < SIZE₁₅
                  && a₁₆[i₄] == 1))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || a₁₆[i₄] == a[i₄])
        && 0 <= i₁₉
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₉
                 ==> i₈ < SIZE₁₅))
        && 0 <= i₂₁
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₂₁
                 ==> i₁₂ < SIZE₁₅))
         ==> i₂₁ < SIZE₁₅
          || i₁₉ < SIZE₁₅
          || i₁₇ < SIZE₁₅
          || sum₂₀ == 0));

