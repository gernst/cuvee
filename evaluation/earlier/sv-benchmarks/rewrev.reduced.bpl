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
        && (forall i₄₃: int ::
              (  i₁₁ < i₄₃
                && i₄₃ <= SIZE₉ - 2
                 ==> 0 <= i₄₃
                    && -1 <= i₄₃
                    && a₁₀[1 + i₄₃] == 3
                    &&   i₄₃ == 1 + i₄₃
                      || a₁₀[i₄₃] == 7
                  ||   (0 <= i₄₃
                       ==> false)
                    && -1 <= i₄₃
                    && a₁₀[1 + i₄₃] == 3))
        && (forall i₄₄: int ::
                  i₁₁ < i₄₄
                  && i₄₄ <= SIZE₉ - 2
                ||   a₁₀[1 + i₄₄] == a[1 + i₄₄]
                  && a₁₀[i₄₄] == a[i₄₄])
        && -1 <= i₁₁
        && 0 <= i₁₁
        && i₁₁ - 1 < i₄
        && i₄ <= SIZE₉ - 2
        && 0 <= i₄
         ==> 0 <= i₄
          && -1 <= i₄
          && a₁₀[i₁₁ := 7][i₁₁ + 1 := 3][1 + i₄] == 3
          &&   i₄ == 1 + i₄
            || a₁₀[i₁₁ := 7][i₁₁ + 1 := 3][i₄] == 7));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 2
        && (forall i₅₀: int ::
              (  i₁₁ < i₅₀
                && i₅₀ <= SIZE₉ - 2
                 ==> 0 <= i₅₀
                    && -1 <= i₅₀
                    && a₁₀[1 + i₅₀] == 3
                    &&   i₅₀ == 1 + i₅₀
                      || a₁₀[i₅₀] == 7
                  ||   (0 <= i₅₀
                       ==> false)
                    && -1 <= i₅₀
                    && a₁₀[1 + i₅₀] == 3))
        && (forall i₅₁: int ::
                  i₁₁ < i₅₁
                  && i₅₁ <= SIZE₉ - 2
                ||   a₁₀[1 + i₅₁] == a[1 + i₅₁]
                  && a₁₀[i₅₁] == a[i₅₁])
        && -1 <= i₁₁
        && 0 <= i₁₁
         ==> i₁₁ - 1 < i₄
          || a₁₀[i₁₁ := 7][i₁₁ + 1 := 3][1 + i₄] == a[1 + i₄]));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 2
        && (forall i₆₇: int ::
              (  i₁₁ < i₆₇
                && i₆₇ <= SIZE₉ - 2
                 ==> 0 <= i₆₇
                    && -1 <= i₆₇
                    && a₁₀[1 + i₆₇] == 3
                    &&   i₆₇ == 1 + i₆₇
                      || a₁₀[i₆₇] == 7
                  ||   (0 <= i₆₇
                       ==> false)
                    && -1 <= i₆₇
                    && a₁₀[1 + i₆₇] == 3))
        && (forall i₆₈: int ::
                  i₁₁ < i₆₈
                  && i₆₈ <= SIZE₉ - 2
                ||   a₁₀[1 + i₆₈] == a[1 + i₆₈]
                  && a₁₀[i₆₈] == a[i₆₈])
        && -1 <= i₁₁
        && 0 <= i₁₁
         ==> i₄ <= SIZE₉ - 2
          || a₁₀[i₁₁ := 7][i₁₁ + 1 := 3][i₄] == a[i₄]));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  1 < SIZE₉
        && SIZE₉ < 100000
        && i₁₁ <= SIZE₉ - 2
        && (forall i₇₈: int ::
              (  i₁₁ < i₇₈
                && i₇₈ <= SIZE₉ - 2
                 ==> 0 <= i₇₈
                    && -1 <= i₇₈
                    && a₁₀[1 + i₇₈] == 3
                    &&   i₇₈ == 1 + i₇₈
                      || a₁₀[i₇₈] == 7
                  ||   (0 <= i₇₈
                       ==> false)
                    && -1 <= i₇₈
                    && a₁₀[1 + i₇₈] == 3))
        && (forall i₇₉: int ::
                  i₁₁ < i₇₉
                  && i₇₉ <= SIZE₉ - 2
                ||   a₁₀[1 + i₇₉] == a[1 + i₇₉]
                  && a₁₀[i₇₉] == a[i₇₉])
        && -1 <= i₁₁
        && i₁₁ - 1 < i₄
        && i₄ <= SIZE₉ - 2
         ==> 0 <= i₁₁
          ||   0 <= i₄
            && -1 <= i₄
            && a₁₀[i₁₁ + 1 := 3][1 + i₄] == 3
            &&   i₄ == 1 + i₄
              || a₁₀[i₁₁ + 1 := 3][i₄] == 7
          ||   (0 <= i₄
               ==> false)
            && -1 <= i₄
            && a₁₀[i₁₁ + 1 := 3][1 + i₄] == 3));

