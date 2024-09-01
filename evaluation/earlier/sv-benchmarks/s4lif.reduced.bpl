data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₇: int, sum: [int]int, a: [int]int, a₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, x₁₄: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && i₁₉ <= N₁₇
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₉
                 ==> (exists i₅: int ::
                        i₅ < N₁₇
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₉
                        && a₁₈[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₉)
                || a₁₈[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₁₉
                 ==> i₅ < N₁₇))
        && 0 <= i₂₁
        && i₂₁ <= N₁₇
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₂₁
                 ==> (exists i₉: int ::
                          a₂₀[i₉] == 1
                          && i₉ < N₁₇
                          && x₁₀ == i₉
                          && 0 <= i₉
                          && i₉ < i₂₁
                          && a₂₀[x₁₀] == 4 + a₁₈[i₉])
                  || (exists i₉: int ::
                        (a₂₀[i₉] == 1
                           ==> false))))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₁)
                || a₂₀[x₁₀] == a₁₈[x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₂₁
                 ==> i₉ < N₁₇))
        && x₁₄ == 0
         ==> i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || (exists i₁₃: int ::
                  i₁₃ < N₁₇
                  && x₁₄ == 0
                  && sum[0 := 0][x₁₄] == a₂₀[i₁₃] + sum[0 := 0][0])));

goal (forall N₁₇: int, sum: [int]int, a: [int]int, a₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, sum₂₂: [int]int, i₂₃: int, x₁₄: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && i₁₉ <= N₁₇
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₉
                 ==> (exists i₅: int ::
                        i₅ < N₁₇
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₉
                        && a₁₈[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₉)
                || a₁₈[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₁₉
                 ==> i₅ < N₁₇))
        && 0 <= i₂₁
        && i₂₁ <= N₁₇
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₂₁
                 ==> (exists i₉: int ::
                          a₂₀[i₉] == 1
                          && i₉ < N₁₇
                          && x₁₀ == i₉
                          && 0 <= i₉
                          && i₉ < i₂₁
                          && a₂₀[x₁₀] == 4 + a₁₈[i₉])
                  || (exists i₉: int ::
                        (a₂₀[i₉] == 1
                           ==> false))))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₁)
                || a₂₀[x₁₀] == a₁₈[x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₂₁
                 ==> i₉ < N₁₇))
        && 0 <= i₂₃
        && i₂₃ <= N₁₇
        && (forall x₂₂₂: int ::
              (x₂₂₂ == 0
                 ==> (exists i₁₃: int ::
                        i₁₃ < N₁₇
                        && x₂₂₂ == 0
                        && sum₂₂[x₂₂₂] == a₂₀[i₁₃] + sum[0 := 0][0])))
        && (forall x₂₂₃: int ::
                x₂₂₃ == 0
                || sum₂₂[x₂₂₃] == sum[0 := 0][x₂₂₃])
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₃
                 ==> i₁₃ < N₁₇))
        && i₂₃ < N₁₇
        && x₁₄ == 0
         ==> i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || (exists i₁₃: int ::
                  i₁₃ < N₁₇
                  && x₁₄ == 0
                  && sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][x₁₄] == a₂₀[i₁₃] + sum[0 := 0][0])));

goal (forall N₁₇: int, sum: [int]int, a: [int]int, a₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, sum₂₂: [int]int, i₂₃: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && i₁₉ <= N₁₇
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₉
                 ==> (exists i₅: int ::
                        i₅ < N₁₇
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₉
                        && a₁₈[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₉)
                || a₁₈[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₁₉
                 ==> i₅ < N₁₇))
        && 0 <= i₂₁
        && i₂₁ <= N₁₇
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₂₁
                 ==> (exists i₉: int ::
                          a₂₀[i₉] == 1
                          && i₉ < N₁₇
                          && x₁₀ == i₉
                          && 0 <= i₉
                          && i₉ < i₂₁
                          && a₂₀[x₁₀] == 4 + a₁₈[i₉])
                  || (exists i₉: int ::
                        (a₂₀[i₉] == 1
                           ==> false))))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₁)
                || a₂₀[x₁₀] == a₁₈[x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₂₁
                 ==> i₉ < N₁₇))
        && 0 <= i₂₃
        && i₂₃ <= N₁₇
        && (forall x₁₄: int ::
              (x₁₄ == 0
                 ==> (exists i₁₃: int ::
                        i₁₃ < N₁₇
                        && x₁₄ == 0
                        && sum₂₂[x₁₄] == a₂₀[i₁₃] + sum[0 := 0][0])))
        && (forall x₁₄: int ::
                x₁₄ == 0
                || sum₂₂[x₁₄] == sum[0 := 0][x₁₄])
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₃
                 ==> i₁₃ < N₁₇))
         ==> i₂₃ < N₁₇
          || i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || sum₂₂[0] == 5 * N₁₇));

