data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₅: int, a: [int]int, sum: [int]int, a₂₆: [int]int, i₂₇: int, a₂₈: [int]int, i₂₉: int, a₃₀: [int]int, i₃₁: int, a₃₂: [int]int, i₃₃: int, x₂₂: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && i₂₇ <= N₂₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₇
                 ==> (exists i₅: int ::
                        i₅ < N₂₅
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₇
                        && a₂₆[x₆] == 1 + i₅ * i₅ + 2 * i₅)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₇)
                || a₂₆[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₇
                 ==> i₅ < N₂₅))
        && 0 <= i₂₉
        && i₂₉ <= N₂₅
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₂₉
                 ==> (exists i₉: int ::
                        i₉ < N₂₅
                        && x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₉
                        && a₂₈[x₁₀] == a₂₆[i₉] + -(i₉ * i₉))))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₉)
                || a₂₈[x₁₀] == a₂₆[x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₂₉
                 ==> i₉ < N₂₅))
        && 0 <= i₃₁
        && i₃₁ <= N₂₅
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> (exists i₁₃: int ::
                        i₁₃ < N₂₅
                        && x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₃₁
                        && a₃₀[x₁₄] == -i₁₃ + a₂₈[i₁₃])))
        && (forall x₁₄: int ::
                (exists i₁₃: int ::
                        x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₃₁)
                || a₃₀[x₁₄] == a₂₈[x₁₄])
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> i₁₃ < N₂₅))
        && 0 <= i₃₃
        && i₃₃ <= N₂₅
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> (exists i₁₇: int ::
                        i₁₇ < N₂₅
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₃
                        && a₃₂[x₁₈] == -i₁₇ + a₃₀[i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₃)
                || a₃₂[x₁₈] == a₃₀[x₁₈])
        && (forall i₁₇: int ::
              (  i₁₇ <= i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> i₁₇ < N₂₅))
        && x₂₂ == 0
         ==> i₃₃ < N₂₅
          || i₃₁ < N₂₅
          || i₂₉ < N₂₅
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || (exists i₂₁: int ::
                  i₂₁ < N₂₅
                  && x₂₂ == 0
                  && sum[0 := 0][x₂₂] == a₃₂[i₂₁] + sum[0 := 0][0])));

goal (forall N₂₅: int, a: [int]int, sum: [int]int, a₂₆: [int]int, i₂₇: int, a₂₈: [int]int, i₂₉: int, a₃₀: [int]int, i₃₁: int, a₃₂: [int]int, i₃₃: int, sum₃₄: [int]int, i₃₅: int, x₂₂: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && i₂₇ <= N₂₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₇
                 ==> (exists i₅: int ::
                        i₅ < N₂₅
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₇
                        && a₂₆[x₆] == 1 + i₅ * i₅ + 2 * i₅)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₇)
                || a₂₆[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₇
                 ==> i₅ < N₂₅))
        && 0 <= i₂₉
        && i₂₉ <= N₂₅
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₂₉
                 ==> (exists i₉: int ::
                        i₉ < N₂₅
                        && x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₉
                        && a₂₈[x₁₀] == a₂₆[i₉] + -(i₉ * i₉))))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₉)
                || a₂₈[x₁₀] == a₂₆[x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₂₉
                 ==> i₉ < N₂₅))
        && 0 <= i₃₁
        && i₃₁ <= N₂₅
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> (exists i₁₃: int ::
                        i₁₃ < N₂₅
                        && x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₃₁
                        && a₃₀[x₁₄] == -i₁₃ + a₂₈[i₁₃])))
        && (forall x₁₄: int ::
                (exists i₁₃: int ::
                        x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₃₁)
                || a₃₀[x₁₄] == a₂₈[x₁₄])
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> i₁₃ < N₂₅))
        && 0 <= i₃₃
        && i₃₃ <= N₂₅
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> (exists i₁₇: int ::
                        i₁₇ < N₂₅
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₃
                        && a₃₂[x₁₈] == -i₁₇ + a₃₀[i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₃)
                || a₃₂[x₁₈] == a₃₀[x₁₈])
        && (forall i₁₇: int ::
              (  i₁₇ <= i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> i₁₇ < N₂₅))
        && 0 <= i₃₅
        && i₃₅ <= N₂₅
        && (forall x₄₁₀: int ::
              (x₄₁₀ == 0
                 ==> (exists i₂₁: int ::
                        i₂₁ < N₂₅
                        && x₄₁₀ == 0
                        && sum₃₄[x₄₁₀] == a₃₂[i₂₁] + sum[0 := 0][0])))
        && (forall x₄₁₁: int ::
                x₄₁₁ == 0
                || sum₃₄[x₄₁₁] == sum[0 := 0][x₄₁₁])
        && (forall i₂₁: int ::
              (  i₂₁ <= i₂₁
                && 0 <= i₂₁
                && i₂₁ < i₃₅
                 ==> i₂₁ < N₂₅))
        && i₃₅ < N₂₅
        && x₂₂ == 0
         ==> i₃₃ < N₂₅
          || i₃₁ < N₂₅
          || i₂₉ < N₂₅
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || (exists i₂₁: int ::
                  i₂₁ < N₂₅
                  && x₂₂ == 0
                  && sum₃₄[0 := sum₃₄[0] + a₃₂[i₃₅]][x₂₂] == a₃₂[i₂₁] + sum[0 := 0][0])));

goal (forall N₂₅: int, a: [int]int, sum: [int]int, a₂₆: [int]int, i₂₇: int, a₂₈: [int]int, i₂₉: int, a₃₀: [int]int, i₃₁: int, a₃₂: [int]int, i₃₃: int, sum₃₄: [int]int, i₃₅: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && i₂₇ <= N₂₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₇
                 ==> (exists i₅: int ::
                        i₅ < N₂₅
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₇
                        && a₂₆[x₆] == 1 + i₅ * i₅ + 2 * i₅)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₇)
                || a₂₆[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₇
                 ==> i₅ < N₂₅))
        && 0 <= i₂₉
        && i₂₉ <= N₂₅
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₂₉
                 ==> (exists i₉: int ::
                        i₉ < N₂₅
                        && x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₉
                        && a₂₈[x₁₀] == a₂₆[i₉] + -(i₉ * i₉))))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₂₉)
                || a₂₈[x₁₀] == a₂₆[x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₂₉
                 ==> i₉ < N₂₅))
        && 0 <= i₃₁
        && i₃₁ <= N₂₅
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> (exists i₁₃: int ::
                        i₁₃ < N₂₅
                        && x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₃₁
                        && a₃₀[x₁₄] == -i₁₃ + a₂₈[i₁₃])))
        && (forall x₁₄: int ::
                (exists i₁₃: int ::
                        x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₃₁)
                || a₃₀[x₁₄] == a₂₈[x₁₄])
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> i₁₃ < N₂₅))
        && 0 <= i₃₃
        && i₃₃ <= N₂₅
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> (exists i₁₇: int ::
                        i₁₇ < N₂₅
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₃
                        && a₃₂[x₁₈] == -i₁₇ + a₃₀[i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₃)
                || a₃₂[x₁₈] == a₃₀[x₁₈])
        && (forall i₁₇: int ::
              (  i₁₇ <= i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> i₁₇ < N₂₅))
        && 0 <= i₃₅
        && i₃₅ <= N₂₅
        && (forall x₂₂: int ::
              (x₂₂ == 0
                 ==> (exists i₂₁: int ::
                        i₂₁ < N₂₅
                        && x₂₂ == 0
                        && sum₃₄[x₂₂] == a₃₂[i₂₁] + sum[0 := 0][0])))
        && (forall x₂₂: int ::
                x₂₂ == 0
                || sum₃₄[x₂₂] == sum[0 := 0][x₂₂])
        && (forall i₂₁: int ::
              (  i₂₁ <= i₂₁
                && 0 <= i₂₁
                && i₂₁ < i₃₅
                 ==> i₂₁ < N₂₅))
         ==> i₃₅ < N₂₅
          || i₃₃ < N₂₅
          || i₃₁ < N₂₅
          || i₂₉ < N₂₅
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₃₄[0] == N₂₅));

