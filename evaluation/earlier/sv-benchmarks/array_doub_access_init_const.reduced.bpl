data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall a: [int]int, a₈: [int]int, i₉: int, i₁₀: int ::
      (  0 <= i₉
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₉
                 ==> i₃ <= 100000
                  && a₈[1 + 2 * i₃] == 0
                  &&   2 * i₃ == 1 + 2 * i₃
                    || a₈[2 * i₃] == 0))
        && (forall i₃: int ::
                  0 <= i₃
                  && i₃ < i₉
                ||   a₈[1 + 2 * i₃] == a[1 + 2 * i₃]
                  && a₈[2 * i₃] == a[2 * i₃])
        && 0 <= i₁₀
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₀
                 ==> i₆ <= 2 * 100000))
        && i₁₀ <= 2 * 100000
         ==> i₉ <= 100000
          || 0 <= a₈[i₁₀]));

