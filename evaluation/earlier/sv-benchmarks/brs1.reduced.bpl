data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, sum: [int]int, a: [int]int, a₁₄: [int]int, i₁₅: int, sum₁₆: [int]int, i₁₇: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₅
                 ==> (exists i₅: int ::
                          i₅ % 1 == 0
                          && i₅ < N₁₃
                          && x₆ == i₅
                          && 0 <= i₅
                          && i₅ < i₁₅
                          && a₁₄[x₆] == 1)
                  || (exists i₅: int ::
                        (i₅ % 1 == 0
                           ==> false))))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₅)
                || a₁₄[x₆] == a[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ < N₁₃))
        && 0 <= i₁₇
        && i₁₇ <= N₁₃
        && (forall x₁₀: int ::
              (x₁₀ == 0
                 ==> (exists i₉: int ::
                          i₉ == 0
                          && i₉ < N₁₃
                          && x₁₀ == 0
                          && sum₁₆[x₁₀] == 0)
                  || (exists i₉: int ::
                        (i₉ == 0
                           ==> false))))
        && (forall x₁₀: int ::
                x₁₀ == 0
                || sum₁₆[x₁₀] == sum[x₁₀])
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₁₇
                 ==> i₉ < N₁₃))
         ==> i₁₇ < N₁₃
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || sum₁₆[0] <= N₁₃));

