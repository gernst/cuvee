data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₄₇: int, a: [int]int, a₄₈: [int]int, i₄₉: int, i₅₁: int, i₅₃: int, i₅₅: int, i₅₇: int, i₅₉: int, i₆₁: int, i₆₃: int, i₆₅: int, i₆₇: int, sum₆₈: int, i₆₉: int ::
      (  1 < SIZE₄₇
        && SIZE₄₇ < 100000
        && 0 <= i₄₉
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₉
                 ==> i₄ < SIZE₄₇
                  && a₄₈[i₄] == 1))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₄₉
                || a₄₈[i₄] == a[i₄])
        && 0 <= i₅₁
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₅₁
                 ==> i₈ < SIZE₄₇))
        && 0 <= i₅₃
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₅₃
                 ==> i₁₂ < SIZE₄₇))
        && 0 <= i₅₅
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₅₅
                 ==> i₁₆ < SIZE₄₇))
        && 0 <= i₅₇
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₅₇
                 ==> i₂₀ < SIZE₄₇))
        && 0 <= i₅₉
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₅₉
                 ==> i₂₄ < SIZE₄₇))
        && 0 <= i₆₁
        && (forall i₂₈: int ::
              (  0 <= i₂₈
                && i₂₈ < i₆₁
                 ==> i₂₈ < SIZE₄₇))
        && 0 <= i₆₃
        && (forall i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ < i₆₃
                 ==> i₃₂ < SIZE₄₇))
        && 0 <= i₆₅
        && (forall i₃₆: int ::
              (  0 <= i₃₆
                && i₃₆ < i₆₅
                 ==> i₃₆ < SIZE₄₇))
        && 0 <= i₆₇
        && (forall i₄₀: int ::
              (  0 <= i₄₀
                && i₄₀ < i₆₇
                 ==> i₄₀ < SIZE₄₇))
        && 0 <= i₆₉
        && (forall i₄₄: int ::
              (  0 <= i₄₄
                && i₄₄ < i₆₉
                 ==> i₄₄ < SIZE₄₇))
         ==> i₆₉ < SIZE₄₇
          || i₆₇ < SIZE₄₇
          || i₆₅ < SIZE₄₇
          || i₆₃ < SIZE₄₇
          || i₆₁ < SIZE₄₇
          || i₅₉ < SIZE₄₇
          || i₅₇ < SIZE₄₇
          || i₅₅ < SIZE₄₇
          || i₅₃ < SIZE₄₇
          || i₅₁ < SIZE₄₇
          || i₄₉ < SIZE₄₇
          || sum₆₈ == 0));

