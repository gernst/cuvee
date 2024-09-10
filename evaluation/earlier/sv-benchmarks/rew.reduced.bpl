data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  -2147483648 <= SIZE₉
        && SIZE₉ < 2147483648
        && 1 < SIZE₉
        && SIZE₉ < 100000
        && 0 <= i₁₁
        && (forall i₄₃: int ::
              (  0 <= i₄₃
                && i₄₃ < i₁₁
                 ==> 1 + i₄₃ < SIZE₉
                    && i₄₃ < SIZE₉
                    && a₁₀[i₄₃] == 3
                    &&   1 + i₄₃ == i₄₃
                      || a₁₀[1 + i₄₃] == 0
                  ||   (1 + i₄₃ < SIZE₉
                       ==> false)
                    && i₄₃ < SIZE₉
                    && a₁₀[i₄₃] == 3))
        && (forall i₄₄: int ::
                  0 <= i₄₄
                  && i₄₄ < i₁₁
                ||   a₁₀[i₄₄] == a[i₄₄]
                  && a₁₀[1 + i₄₄] == a[1 + i₄₄])
        && i₁₁ < SIZE₉
        && i₁₁ + 1 < SIZE₉
        && 0 <= i₄
        && i₄ < i₁₁ + 1
        && 1 + i₄ < SIZE₉
         ==> 1 + i₄ < SIZE₉
          && i₄ < SIZE₉
          && a₁₀[i₁₁ + 1 := 0][i₁₁ := 3][i₄] == 3
          &&   1 + i₄ == i₄
            || a₁₀[i₁₁ + 1 := 0][i₁₁ := 3][1 + i₄] == 0));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  -2147483648 <= SIZE₉
        && SIZE₉ < 2147483648
        && 1 < SIZE₉
        && SIZE₉ < 100000
        && 0 <= i₁₁
        && (forall i₅₅: int ::
              (  0 <= i₅₅
                && i₅₅ < i₁₁
                 ==> 1 + i₅₅ < SIZE₉
                    && i₅₅ < SIZE₉
                    && a₁₀[i₅₅] == 3
                    &&   1 + i₅₅ == i₅₅
                      || a₁₀[1 + i₅₅] == 0
                  ||   (1 + i₅₅ < SIZE₉
                       ==> false)
                    && i₅₅ < SIZE₉
                    && a₁₀[i₅₅] == 3))
        && (forall i₅₆: int ::
                  0 <= i₅₆
                  && i₅₆ < i₁₁
                ||   a₁₀[i₅₆] == a[i₅₆]
                  && a₁₀[1 + i₅₆] == a[1 + i₅₆])
        && i₁₁ < SIZE₉
        && i₁₁ + 1 < SIZE₉
         ==> 0 <= i₄
          || a₁₀[i₁₁ + 1 := 0][i₁₁ := 3][1 + i₄] == a[1 + i₄]));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  -2147483648 <= SIZE₉
        && SIZE₉ < 2147483648
        && 1 < SIZE₉
        && SIZE₉ < 100000
        && 0 <= i₁₁
        && (forall i₆₂: int ::
              (  0 <= i₆₂
                && i₆₂ < i₁₁
                 ==> 1 + i₆₂ < SIZE₉
                    && i₆₂ < SIZE₉
                    && a₁₀[i₆₂] == 3
                    &&   1 + i₆₂ == i₆₂
                      || a₁₀[1 + i₆₂] == 0
                  ||   (1 + i₆₂ < SIZE₉
                       ==> false)
                    && i₆₂ < SIZE₉
                    && a₁₀[i₆₂] == 3))
        && (forall i₆₃: int ::
                  0 <= i₆₃
                  && i₆₃ < i₁₁
                ||   a₁₀[i₆₃] == a[i₆₃]
                  && a₁₀[1 + i₆₃] == a[1 + i₆₃])
        && i₁₁ < SIZE₉
        && i₁₁ + 1 < SIZE₉
         ==> i₄ < i₁₁ + 1
          || a₁₀[i₁₁ + 1 := 0][i₁₁ := 3][i₄] == a[i₄]));

goal {:named "invariant forward"} (forall SIZE₉: int, a: [int]int, a₁₀: [int]int, i₁₁: int, i₄: int ::
      (  -2147483648 <= SIZE₉
        && SIZE₉ < 2147483648
        && 1 < SIZE₉
        && SIZE₉ < 100000
        && 0 <= i₁₁
        && (forall i₇₈: int ::
              (  0 <= i₇₈
                && i₇₈ < i₁₁
                 ==> 1 + i₇₈ < SIZE₉
                    && i₇₈ < SIZE₉
                    && a₁₀[i₇₈] == 3
                    &&   1 + i₇₈ == i₇₈
                      || a₁₀[1 + i₇₈] == 0
                  ||   (1 + i₇₈ < SIZE₉
                       ==> false)
                    && i₇₈ < SIZE₉
                    && a₁₀[i₇₈] == 3))
        && (forall i₇₉: int ::
                  0 <= i₇₉
                  && i₇₉ < i₁₁
                ||   a₁₀[i₇₉] == a[i₇₉]
                  && a₁₀[1 + i₇₉] == a[1 + i₇₉])
        && i₁₁ < SIZE₉
        && 0 <= i₄
        && i₄ < i₁₁ + 1
         ==> i₁₁ + 1 < SIZE₉
          ||   1 + i₄ < SIZE₉
            && i₄ < SIZE₉
            && a₁₀[i₁₁ := 3][i₄] == 3
            &&   1 + i₄ == i₄
              || a₁₀[i₁₁ := 3][1 + i₄] == 0
          ||   (1 + i₄ < SIZE₉
               ==> false)
            && i₄ < SIZE₉
            && a₁₀[i₁₁ := 3][i₄] == 3));

