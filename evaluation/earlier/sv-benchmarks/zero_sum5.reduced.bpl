data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₄₈: int, a: [int]int, a₅₀: [int]int, i₅₁: int, i₅₃: int, i₅₅: int, i₅₇: int, i₅₉: int, i₆₁: int, i₆₃: int, i₆₅: int, i₆₇: int, i₆₉: int, sum₇₀: int, i₇₁: int ::
      (  1 < SIZE₄₈
        && 0 <= i₅₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₁
                 ==> (exists nondet_short₁₄: int ::
                        i₅ < SIZE₄₈
                        && a₅₀[i₅] == nondet_short₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₅₁
                || a₅₀[i₅] == a[i₅])
        && 0 <= i₅₃
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₅₃
                 ==> i₉ < SIZE₄₈))
        && 0 <= i₅₅
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₅₅
                 ==> i₁₃ < SIZE₄₈))
        && 0 <= i₅₇
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₅₇
                 ==> i₁₇ < SIZE₄₈))
        && 0 <= i₅₉
        && (forall i₂₁: int ::
              (  0 <= i₂₁
                && i₂₁ < i₅₉
                 ==> i₂₁ < SIZE₄₈))
        && 0 <= i₆₁
        && (forall i₂₅: int ::
              (  0 <= i₂₅
                && i₂₅ < i₆₁
                 ==> i₂₅ < SIZE₄₈))
        && 0 <= i₆₃
        && (forall i₂₉: int ::
              (  0 <= i₂₉
                && i₂₉ < i₆₃
                 ==> i₂₉ < SIZE₄₈))
        && 0 <= i₆₅
        && (forall i₃₃: int ::
              (  0 <= i₃₃
                && i₃₃ < i₆₅
                 ==> i₃₃ < SIZE₄₈))
        && 0 <= i₆₇
        && (forall i₃₇: int ::
              (  0 <= i₃₇
                && i₃₇ < i₆₇
                 ==> i₃₇ < SIZE₄₈))
        && 0 <= i₆₉
        && (forall i₄₁: int ::
              (  0 <= i₄₁
                && i₄₁ < i₆₉
                 ==> i₄₁ < SIZE₄₈))
        && 0 <= i₇₁
        && (forall i₄₅: int ::
              (  0 <= i₄₅
                && i₄₅ < i₇₁
                 ==> i₄₅ < SIZE₄₈))
         ==> i₇₁ < SIZE₄₈
          || i₆₉ < SIZE₄₈
          || i₆₇ < SIZE₄₈
          || i₆₅ < SIZE₄₈
          || i₆₃ < SIZE₄₈
          || i₆₁ < SIZE₄₈
          || i₅₉ < SIZE₄₈
          || i₅₇ < SIZE₄₈
          || i₅₅ < SIZE₄₈
          || i₅₃ < SIZE₄₈
          || i₅₁ < SIZE₄₈
          || sum₇₀ == 0));

