data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 2
        && (forall i₆₁: int ::
              (  i₁₁ < i₆₁
                && i₆₁ <= SIZE₉ - 2
                 ==> 0 <= i₆₁
                  && a₁₀[1 + i₆₁] == 1 + i₆₁
                  &&   i₆₁ == 1 + i₆₁
                    || a₁₀[i₆₁] == i₆₁))
        && (forall i₆₂: int ::
                  i₁₁ < i₆₂
                  && i₆₂ <= SIZE₉ - 2
                ||   a₁₀[1 + i₆₂] == a[1 + i₆₂]
                  && a₁₀[i₆₂] == a[i₆₂])
        && 0 <= i₁₁
         ==> i₁₁ - 1 < i₄
          || a₁₀[i₁₁ := i₁₁][i₁₁ + 1 := i₁₁ + 1][1 + i₄] == a[1 + i₄]));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 2
        && (forall i₇₈: int ::
              (  i₁₁ < i₇₈
                && i₇₈ <= SIZE₉ - 2
                 ==> 0 <= i₇₈
                  && a₁₀[1 + i₇₈] == 1 + i₇₈
                  &&   i₇₈ == 1 + i₇₈
                    || a₁₀[i₇₈] == i₇₈))
        && (forall i₇₉: int ::
                  i₁₁ < i₇₉
                  && i₇₉ <= SIZE₉ - 2
                ||   a₁₀[1 + i₇₉] == a[1 + i₇₉]
                  && a₁₀[i₇₉] == a[i₇₉])
        && 0 <= i₁₁
         ==> i₄ <= SIZE₉ - 2
          || a₁₀[i₁₁ := i₁₁][i₁₁ + 1 := i₁₁ + 1][i₄] == a[i₄]));

