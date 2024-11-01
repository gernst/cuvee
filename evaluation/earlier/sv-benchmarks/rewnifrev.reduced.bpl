data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 1
        && (forall i₄₃: int ::
              (  i₁₁ < i₄₃
                && i₄₃ <= SIZE₉ - 1
                 ==> 0 <= -1 + i₄₃
                    && 0 <= i₄₃
                    && a₁₀[i₄₃] == i₄₃
                    &&   -1 + i₄₃ == i₄₃
                      || a₁₀[-1 + i₄₃] == -2 + i₄₃
                  ||   (0 <= -1 + i₄₃
                       ==> false)
                    && 0 <= i₄₃
                    && a₁₀[i₄₃] == i₄₃))
        && (forall i₄₄: int ::
                  i₁₁ < i₄₄
                  && i₄₄ <= SIZE₉ - 1
                ||   a₁₀[i₄₄] == a[i₄₄]
                  && a₁₀[-1 + i₄₄] == a[-1 + i₄₄])
        && 0 <= i₁₁
        && 0 <= i₁₁ - 1
        && i₁₁ - 1 < i₄
        && i₄ <= SIZE₉ - 1
        && 0 <= -1 + i₄
         ==> 0 <= -1 + i₄
          && 0 <= i₄
          && a₁₀[i₁₁ - 1 := i₁₁ - 2][i₁₁ := i₁₁][i₄] == i₄
          &&   -1 + i₄ == i₄
            || a₁₀[i₁₁ - 1 := i₁₁ - 2][i₁₁ := i₁₁][-1 + i₄] == -2 + i₄));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 1
        && (forall i₅₀: int ::
              (  i₁₁ < i₅₀
                && i₅₀ <= SIZE₉ - 1
                 ==> 0 <= -1 + i₅₀
                    && 0 <= i₅₀
                    && a₁₀[i₅₀] == i₅₀
                    &&   -1 + i₅₀ == i₅₀
                      || a₁₀[-1 + i₅₀] == -2 + i₅₀
                  ||   (0 <= -1 + i₅₀
                       ==> false)
                    && 0 <= i₅₀
                    && a₁₀[i₅₀] == i₅₀))
        && (forall i₅₁: int ::
                  i₁₁ < i₅₁
                  && i₅₁ <= SIZE₉ - 1
                ||   a₁₀[i₅₁] == a[i₅₁]
                  && a₁₀[-1 + i₅₁] == a[-1 + i₅₁])
        && 0 <= i₁₁
        && 0 <= i₁₁ - 1
         ==> i₁₁ - 1 < i₄
          || a₁₀[i₁₁ - 1 := i₁₁ - 2][i₁₁ := i₁₁][i₄] == a[i₄]));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 1
        && (forall i₆₇: int ::
              (  i₁₁ < i₆₇
                && i₆₇ <= SIZE₉ - 1
                 ==> 0 <= -1 + i₆₇
                    && 0 <= i₆₇
                    && a₁₀[i₆₇] == i₆₇
                    &&   -1 + i₆₇ == i₆₇
                      || a₁₀[-1 + i₆₇] == -2 + i₆₇
                  ||   (0 <= -1 + i₆₇
                       ==> false)
                    && 0 <= i₆₇
                    && a₁₀[i₆₇] == i₆₇))
        && (forall i₆₈: int ::
                  i₁₁ < i₆₈
                  && i₆₈ <= SIZE₉ - 1
                ||   a₁₀[i₆₈] == a[i₆₈]
                  && a₁₀[-1 + i₆₈] == a[-1 + i₆₈])
        && 0 <= i₁₁
        && 0 <= i₁₁ - 1
         ==> i₄ <= SIZE₉ - 1
          || a₁₀[i₁₁ - 1 := i₁₁ - 2][i₁₁ := i₁₁][-1 + i₄] == a[-1 + i₄]));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 1
        && (forall i₇₈: int ::
              (  i₁₁ < i₇₈
                && i₇₈ <= SIZE₉ - 1
                 ==> 0 <= -1 + i₇₈
                    && 0 <= i₇₈
                    && a₁₀[i₇₈] == i₇₈
                    &&   -1 + i₇₈ == i₇₈
                      || a₁₀[-1 + i₇₈] == -2 + i₇₈
                  ||   (0 <= -1 + i₇₈
                       ==> false)
                    && 0 <= i₇₈
                    && a₁₀[i₇₈] == i₇₈))
        && (forall i₇₉: int ::
                  i₁₁ < i₇₉
                  && i₇₉ <= SIZE₉ - 1
                ||   a₁₀[i₇₉] == a[i₇₉]
                  && a₁₀[-1 + i₇₉] == a[-1 + i₇₉])
        && 0 <= i₁₁
        && i₁₁ - 1 < i₄
        && i₄ <= SIZE₉ - 1
         ==> 0 <= i₁₁ - 1
          ||   0 <= -1 + i₄
            && 0 <= i₄
            && a₁₀[i₁₁ := i₁₁][i₄] == i₄
            &&   -1 + i₄ == i₄
              || a₁₀[i₁₁ := i₁₁][-1 + i₄] == -2 + i₄
          ||   (0 <= -1 + i₄
               ==> false)
            && 0 <= i₄
            && a₁₀[i₁₁ := i₁₁][i₄] == i₄));

