data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, sum: [int]int, a: [int]int, a₁₄: [int]int, i₁₅: int, x₁₀: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₅
                 ==> (exists i₅: int ::
                        i₅ < N₁₃
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₅
                        && a₁₄[x₆] == 4)))
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
        && x₁₀ == 0
         ==> i₁₅ < N₁₃
          || N₁₃ <= 0
          || (exists i₉: int ::
                  a₁₄[i₉] == 4
                  && i₉ < N₁₃
                  && x₁₀ == 0
                  && sum[0 := 0][x₁₀] == a₁₄[i₉] + sum[0 := 0][0])
          || (exists i₉: int ::
                (a₁₄[i₉] == 4
                   ==> false))));

goal (forall N₁₃: int, sum: [int]int, a: [int]int, a₁₄: [int]int, i₁₅: int, sum₁₆: [int]int, i₁₇: int, x₁₀: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₅
                 ==> (exists i₅: int ::
                        i₅ < N₁₃
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₅
                        && a₁₄[x₆] == 4)))
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
        && (forall x₁₀₆: int ::
              (x₁₀₆ == 0
                 ==> (exists i₉: int ::
                          a₁₄[i₉] == 4
                          && i₉ < N₁₃
                          && x₁₀₆ == 0
                          && sum₁₆[x₁₀₆] == a₁₄[i₉] + sum[0 := 0][0])
                  || (exists i₉: int ::
                        (a₁₄[i₉] == 4
                           ==> false))))
        && (forall x₁₀₇: int ::
                x₁₀₇ == 0
                || sum₁₆[x₁₀₇] == sum[0 := 0][x₁₀₇])
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₁₇
                 ==> i₉ < N₁₃))
        && i₁₇ < N₁₃
        && a₁₄[i₁₇] == 4
        && x₁₀ == 0
         ==> i₁₅ < N₁₃
          || N₁₃ <= 0
          || (exists i₉: int ::
                  a₁₄[i₉] == 4
                  && i₉ < N₁₃
                  && x₁₀ == 0
                  && sum₁₆[0 := sum₁₆[0] + a₁₄[i₁₇]][x₁₀] == a₁₄[i₉] + sum[0 := 0][0])
          || (exists i₉: int ::
                (a₁₄[i₉] == 4
                   ==> false))));

goal (forall N₁₃: int, sum: [int]int, a: [int]int, a₁₄: [int]int, i₁₅: int, sum₁₆: [int]int, i₁₇: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₅
                 ==> (exists i₅: int ::
                        i₅ < N₁₃
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₅
                        && a₁₄[x₆] == 4)))
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
                          a₁₄[i₉] == 4
                          && i₉ < N₁₃
                          && x₁₀ == 0
                          && sum₁₆[x₁₀] == a₁₄[i₉] + sum[0 := 0][0])
                  || (exists i₉: int ::
                        (a₁₄[i₉] == 4
                           ==> false))))
        && (forall x₁₀: int ::
                x₁₀ == 0
                || sum₁₆[x₁₀] == sum[0 := 0][x₁₀])
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₁₇
                 ==> i₉ < N₁₃))
         ==> i₁₇ < N₁₃
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || sum₁₆[0] == 4 * N₁₃));

