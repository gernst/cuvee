data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₂₃: int, a: [int]int, a₂₄: [int]int, i₂₅: int, i₂₇: int, i₂₉: int, i₃₁: int, sum₃₂: int, i₃₃: int ::
      (  1 < SIZE₂₃
        && SIZE₂₃ < 100000
        && 0 <= i₂₅
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₂₅
                 ==> i₄ < SIZE₂₃
                  && a₂₄[i₄] == 1))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₂₅
                || a₂₄[i₄] == a[i₄])
        && 0 <= i₂₇
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₂₇
                 ==> i₈ < SIZE₂₃))
        && 0 <= i₂₉
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₂₉
                 ==> i₁₂ < SIZE₂₃))
        && 0 <= i₃₁
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₃₁
                 ==> i₁₆ < SIZE₂₃))
        && 0 <= i₃₃
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₃₃
                 ==> i₂₀ < SIZE₂₃))
         ==> i₃₃ < SIZE₂₃
          || i₃₁ < SIZE₂₃
          || i₂₉ < SIZE₂₃
          || i₂₇ < SIZE₂₃
          || i₂₅ < SIZE₂₃
          || sum₃₂ == 0));

