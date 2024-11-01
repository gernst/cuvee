data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₃₉: int, a: [int]int, a₄₀: [int]int, i₄₁: int, i₄₃: int, i₄₅: int, i₄₇: int, i₄₉: int, i₅₁: int, i₅₃: int, i₅₅: int, sum₅₆: int, i₅₇: int ::
      (  1 < SIZE₃₉
        && SIZE₃₉ < 100000
        && 0 <= i₄₁
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₄₁
                 ==> i₄ < SIZE₃₉
                  && a₄₀[i₄] == 1))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₄₁
                || a₄₀[i₄] == a[i₄])
        && 0 <= i₄₃
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₄₃
                 ==> i₈ < SIZE₃₉))
        && 0 <= i₄₅
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₄₅
                 ==> i₁₂ < SIZE₃₉))
        && 0 <= i₄₇
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₄₇
                 ==> i₁₆ < SIZE₃₉))
        && 0 <= i₄₉
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₄₉
                 ==> i₂₀ < SIZE₃₉))
        && 0 <= i₅₁
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₅₁
                 ==> i₂₄ < SIZE₃₉))
        && 0 <= i₅₃
        && (forall i₂₈: int ::
              (  0 <= i₂₈
                && i₂₈ < i₅₃
                 ==> i₂₈ < SIZE₃₉))
        && 0 <= i₅₅
        && (forall i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ < i₅₅
                 ==> i₃₂ < SIZE₃₉))
        && 0 <= i₅₇
        && (forall i₃₆: int ::
              (  0 <= i₃₆
                && i₃₆ < i₅₇
                 ==> i₃₆ < SIZE₃₉))
         ==> i₅₇ < SIZE₃₉
          || i₅₅ < SIZE₃₉
          || i₅₃ < SIZE₃₉
          || i₅₁ < SIZE₃₉
          || i₄₉ < SIZE₃₉
          || i₄₇ < SIZE₃₉
          || i₄₅ < SIZE₃₉
          || i₄₃ < SIZE₃₉
          || i₄₁ < SIZE₃₉
          || sum₅₆ == 0));

