data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall a: [int]int, a₁₀: [int]int, i₁₁: int, j₁₂: int, i₁₃: int ::
      (  0 <= i₁₁
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₁
                 ==> 1000000 / 2 < i₃
                    && i₃ < 1000000
                    && a₁₀[i₃] == i₃ % 4
                  ||   (1000000 / 2 < i₃
                       ==> false)
                    && i₃ < 1000000
                    && a₁₀[i₃] == 1 + i₃))
        && (forall i₃: int ::
                  0 <= i₃
                  && i₃ < i₁₁
                || a₁₀[i₃] == a[i₃])
        && j₁₂ + 0 == i₁₃ + 0
        && 0 <= j₁₂
        && 0 <= i₁₃
        && (forall j₆: int, i₇: int ::
              (  j₆ + j₆ == i₇ + i₇
                && 0 <= j₆
                && j₆ < j₁₂
                && 0 <= i₇
                && i₇ < i₁₃
                 ==> a₁₀[i₇] == 0
                    && i₇ < 1000000
                  ||   (a₁₀[i₇] == 0
                       ==> false)
                    && i₇ < 1000000))
        && i₁₃ < 1000000
        && a₁₀[i₁₃] == 0
         ==> i₁₁ < 1000000
          || j₁₂ + 1 < 1000000 / 8));

goal {:named "assert"} (forall a: [int]int, a₁₀: [int]int, i₁₁: int, j₁₂: int, i₁₃: int ::
      (  0 <= i₁₁
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₁
                 ==> 1000000 / 2 < i₃
                    && i₃ < 1000000
                    && a₁₀[i₃] == i₃ % 4
                  ||   (1000000 / 2 < i₃
                       ==> false)
                    && i₃ < 1000000
                    && a₁₀[i₃] == 1 + i₃))
        && (forall i₃: int ::
                  0 <= i₃
                  && i₃ < i₁₁
                || a₁₀[i₃] == a[i₃])
        && j₁₂ + 0 == i₁₃ + 0
        && 0 <= j₁₂
        && 0 <= i₁₃
        && (forall j₆: int, i₇: int ::
              (  j₆ + j₆ == i₇ + i₇
                && 0 <= j₆
                && j₆ < j₁₂
                && 0 <= i₇
                && i₇ < i₁₃
                 ==> a₁₀[i₇] == 0
                    && i₇ < 1000000
                  ||   (a₁₀[i₇] == 0
                       ==> false)
                    && i₇ < 1000000))
        && i₁₃ < 1000000
         ==> a₁₀[i₁₃] == 0
          || i₁₁ < 1000000
          || j₁₂ < 1000000 / 8));

goal {:named "invariant forward"} (forall a: [int]int, a₁₀: [int]int, i₁₁: int, j₁₂: int, i₁₃: int ::
      (  0 <= i₁₁
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₁
                 ==> 1000000 / 2 < i₃
                    && i₃ < 1000000
                    && a₁₀[i₃] == i₃ % 4
                  ||   (1000000 / 2 < i₃
                       ==> false)
                    && i₃ < 1000000
                    && a₁₀[i₃] == 1 + i₃))
        && (forall i₃: int ::
                  0 <= i₃
                  && i₃ < i₁₁
                || a₁₀[i₃] == a[i₃])
        && j₁₂ + 0 == i₁₃ + 0
        && 0 <= j₁₂
        && 0 <= i₁₃
        && (forall j₆: int, i₇: int ::
              (  j₆ + j₆ == i₇ + i₇
                && 0 <= j₆
                && j₆ < j₁₂
                && 0 <= i₇
                && i₇ < i₁₃
                 ==> a₁₀[i₇] == 0
                    && i₇ < 1000000
                  ||   (a₁₀[i₇] == 0
                       ==> false)
                    && i₇ < 1000000))
        && i₁₃ < 1000000
         ==> a₁₀[i₁₃] == 0
          || i₁₁ < 1000000
          || j₁₂ + 0 == i₁₃ + 1 + 0));

