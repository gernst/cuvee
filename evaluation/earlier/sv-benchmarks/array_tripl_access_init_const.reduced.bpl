data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, a₈: [int]int, i₉: int, i₁₀: int ::
      (  0 <= i₉
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₉
                 ==> i₃ <= 100000
                  && a₈[2 + 3 * i₃] == 0
                  &&   1 + 3 * i₃ == 2 + 3 * i₃
                    || a₈[1 + 3 * i₃] == 0
                  &&   3 * i₃ == 2 + 3 * i₃
                    || 3 * i₃ == 1 + 3 * i₃
                    || a₈[3 * i₃] == 0))
        && (forall i₃: int ::
                  0 <= i₃
                  && i₃ < i₉
                ||   a₈[2 + 3 * i₃] == a[2 + 3 * i₃]
                  && a₈[1 + 3 * i₃] == a[1 + 3 * i₃]
                  && a₈[3 * i₃] == a[3 * i₃])
        && 0 <= i₁₀
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₀
                 ==> i₆ <= 3 * 100000))
        && i₁₀ <= 3 * 100000
         ==> i₉ <= 100000
          || 0 <= a₈[i₁₀]));

