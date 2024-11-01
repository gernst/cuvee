data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, sum₁₈: int, i₁₉: int ::
      (  0 <= i₁₅
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₅
                 ==> i₄ < 100000
                  && a₁₄[i₄] == i₄))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₅
                || a₁₄[i₄] == a[i₄])
        && 0 <= i₁₇
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₁₇
                 ==> i₇ < 100000
                  && b₁₆[-1 + 100000 + -i₇] == i₇))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₁₇
                || b₁₆[-1 + 100000 + -i₇] == b[-1 + 100000 + -i₇])
        && 0 <= i₁₉
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₁₉
                 ==> i₁₁ < 100000))
         ==> i₁₉ < 100000
          || i₁₇ < 100000
          || i₁₅ < 100000
          || sum₁₈ == 0));

