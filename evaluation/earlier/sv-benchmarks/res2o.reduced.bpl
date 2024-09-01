data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, b₃₄: [int]int, i₃₅: int, c₃₆: [int]int, i₃₇: int, x₂₀: int ::
      (  N₃₁ <= 2147483647 / 4
        && 0 <= i₃₃
        && i₃₃ <= N₃₁
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> (exists i₇: int ::
                        i₇ < N₃₁
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃
                        && a₃₂[x₈] == 1)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃)
                || a₃₂[x₈] == a[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅
                        && b₃₄[x₁₂] == 1)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅)
                || b₃₄[x₁₂] == b[x₁₂])
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> i₁₁ < N₃₁))
        && 0 <= i₃₇
        && i₃₇ <= N₃₁
        && (forall x₁₆: int, i₁₅: int ::
              (  x₁₆ == i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> (exists i₁₅: int ::
                        i₁₅ < N₃₁
                        && x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇
                        && c₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || c₃₆[x₁₆] == c[x₁₆])
        && (forall i₁₅: int ::
              (  i₁₅ <= i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && x₂₀ == 0
         ==> i₃₇ < N₃₁
          || i₃₅ < N₃₁
          || i₃₃ < N₃₁
          || N₃₁ <= 0
          || (exists i₁₉: int ::
                  i₁₉ < N₃₁
                  && x₂₀ == 0
                  && sum[0 := 0][x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, b₃₄: [int]int, i₃₅: int, c₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, x₂₀: int ::
      (  N₃₁ <= 2147483647 / 4
        && 0 <= i₃₃
        && i₃₃ <= N₃₁
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> (exists i₇: int ::
                        i₇ < N₃₁
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃
                        && a₃₂[x₈] == 1)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃)
                || a₃₂[x₈] == a[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅
                        && b₃₄[x₁₂] == 1)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅)
                || b₃₄[x₁₂] == b[x₁₂])
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> i₁₁ < N₃₁))
        && 0 <= i₃₇
        && i₃₇ <= N₃₁
        && (forall x₁₆: int, i₁₅: int ::
              (  x₁₆ == i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> (exists i₁₅: int ::
                        i₁₅ < N₃₁
                        && x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇
                        && c₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || c₃₆[x₁₆] == c[x₁₆])
        && (forall i₁₅: int ::
              (  i₁₅ <= i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₃₄₆: int ::
              (x₃₄₆ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₃₄₆ == 0
                        && sum₃₈[x₃₄₆] == sum[0 := 0][0] + a₃₂[i₁₉])))
        && (forall x₃₄₇: int ::
                x₃₄₇ == 0
                || sum₃₈[x₃₄₇] == sum[0 := 0][x₃₄₇])
        && (forall i₁₉: int ::
              (  i₁₉ <= i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && i₃₉ < N₃₁
        && x₂₀ == 0
         ==> i₃₇ < N₃₁
          || i₃₅ < N₃₁
          || i₃₃ < N₃₁
          || N₃₁ <= 0
          || (exists i₁₉: int ::
                  i₁₉ < N₃₁
                  && x₂₀ == 0
                  && sum₃₈[0 := sum₃₈[0] + a₃₂[i₃₉]][x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, b₃₄: [int]int, i₃₅: int, c₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, x₂₄: int ::
      (  N₃₁ <= 2147483647 / 4
        && 0 <= i₃₃
        && i₃₃ <= N₃₁
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> (exists i₇: int ::
                        i₇ < N₃₁
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃
                        && a₃₂[x₈] == 1)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃)
                || a₃₂[x₈] == a[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅
                        && b₃₄[x₁₂] == 1)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅)
                || b₃₄[x₁₂] == b[x₁₂])
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> i₁₁ < N₃₁))
        && 0 <= i₃₇
        && i₃₇ <= N₃₁
        && (forall x₁₆: int, i₁₅: int ::
              (  x₁₆ == i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> (exists i₁₅: int ::
                        i₁₅ < N₃₁
                        && x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇
                        && c₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || c₃₆[x₁₆] == c[x₁₆])
        && (forall i₁₅: int ::
              (  i₁₅ <= i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₂₀: int ::
              (x₂₀ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₂₀ == 0
                        && sum₃₈[x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])))
        && (forall x₂₀: int ::
                x₂₀ == 0
                || sum₃₈[x₂₀] == sum[0 := 0][x₂₀])
        && (forall i₁₉: int ::
              (  i₁₉ <= i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && x₂₄ == 0
         ==> i₃₉ < N₃₁
          || i₃₇ < N₃₁
          || i₃₅ < N₃₁
          || i₃₃ < N₃₁
          || N₃₁ <= 0
          || (exists i₂₃: int ::
                  i₂₃ < N₃₁
                  && x₂₄ == 0
                  && sum₃₈[x₂₄] == sum₃₈[0] + b₃₄[i₂₃])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, b₃₄: [int]int, i₃₅: int, c₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, sum₄₀: [int]int, i₄₁: int, x₂₄: int ::
      (  N₃₁ <= 2147483647 / 4
        && 0 <= i₃₃
        && i₃₃ <= N₃₁
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> (exists i₇: int ::
                        i₇ < N₃₁
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃
                        && a₃₂[x₈] == 1)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃)
                || a₃₂[x₈] == a[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅
                        && b₃₄[x₁₂] == 1)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅)
                || b₃₄[x₁₂] == b[x₁₂])
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> i₁₁ < N₃₁))
        && 0 <= i₃₇
        && i₃₇ <= N₃₁
        && (forall x₁₆: int, i₁₅: int ::
              (  x₁₆ == i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> (exists i₁₅: int ::
                        i₁₅ < N₃₁
                        && x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇
                        && c₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || c₃₆[x₁₆] == c[x₁₆])
        && (forall i₁₅: int ::
              (  i₁₅ <= i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₂₀: int ::
              (x₂₀ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₂₀ == 0
                        && sum₃₈[x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])))
        && (forall x₂₀: int ::
                x₂₀ == 0
                || sum₃₈[x₂₀] == sum[0 := 0][x₂₀])
        && (forall i₁₉: int ::
              (  i₁₉ <= i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && 0 <= i₄₁
        && i₄₁ <= N₃₁
        && (forall x₄₉₀: int ::
              (x₄₉₀ == 0
                 ==> (exists i₂₃: int ::
                        i₂₃ < N₃₁
                        && x₄₉₀ == 0
                        && sum₄₀[x₄₉₀] == sum₃₈[0] + b₃₄[i₂₃])))
        && (forall x₄₉₁: int ::
                x₄₉₁ == 0
                || sum₄₀[x₄₉₁] == sum₃₈[x₄₉₁])
        && (forall i₂₃: int ::
              (  i₂₃ <= i₂₃
                && 0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> i₂₃ < N₃₁))
        && i₄₁ < N₃₁
        && x₂₄ == 0
         ==> i₃₉ < N₃₁
          || i₃₇ < N₃₁
          || i₃₅ < N₃₁
          || i₃₃ < N₃₁
          || N₃₁ <= 0
          || (exists i₂₃: int ::
                  i₂₃ < N₃₁
                  && x₂₄ == 0
                  && sum₄₀[0 := sum₄₀[0] + b₃₄[i₄₁]][x₂₄] == sum₃₈[0] + b₃₄[i₂₃])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, b₃₄: [int]int, i₃₅: int, c₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, sum₄₀: [int]int, i₄₁: int, x₂₈: int ::
      (  N₃₁ <= 2147483647 / 4
        && 0 <= i₃₃
        && i₃₃ <= N₃₁
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> (exists i₇: int ::
                        i₇ < N₃₁
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃
                        && a₃₂[x₈] == 1)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃)
                || a₃₂[x₈] == a[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅
                        && b₃₄[x₁₂] == 1)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅)
                || b₃₄[x₁₂] == b[x₁₂])
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> i₁₁ < N₃₁))
        && 0 <= i₃₇
        && i₃₇ <= N₃₁
        && (forall x₁₆: int, i₁₅: int ::
              (  x₁₆ == i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> (exists i₁₅: int ::
                        i₁₅ < N₃₁
                        && x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇
                        && c₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || c₃₆[x₁₆] == c[x₁₆])
        && (forall i₁₅: int ::
              (  i₁₅ <= i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₂₀: int ::
              (x₂₀ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₂₀ == 0
                        && sum₃₈[x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])))
        && (forall x₂₀: int ::
                x₂₀ == 0
                || sum₃₈[x₂₀] == sum[0 := 0][x₂₀])
        && (forall i₁₉: int ::
              (  i₁₉ <= i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && 0 <= i₄₁
        && i₄₁ <= N₃₁
        && (forall x₂₄: int ::
              (x₂₄ == 0
                 ==> (exists i₂₃: int ::
                        i₂₃ < N₃₁
                        && x₂₄ == 0
                        && sum₄₀[x₂₄] == sum₃₈[0] + b₃₄[i₂₃])))
        && (forall x₂₄: int ::
                x₂₄ == 0
                || sum₄₀[x₂₄] == sum₃₈[x₂₄])
        && (forall i₂₃: int ::
              (  i₂₃ <= i₂₃
                && 0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> i₂₃ < N₃₁))
        && x₂₈ == 0
         ==> i₄₁ < N₃₁
          || i₃₉ < N₃₁
          || i₃₇ < N₃₁
          || i₃₅ < N₃₁
          || i₃₃ < N₃₁
          || N₃₁ <= 0
          || (exists i₂₇: int ::
                  i₂₇ < N₃₁
                  && x₂₈ == 0
                  && sum₄₀[x₂₈] == sum₄₀[0] + c₃₆[i₂₇])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, b₃₄: [int]int, i₃₅: int, c₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, sum₄₀: [int]int, i₄₁: int, sum₄₂: [int]int, i₄₃: int, x₂₈: int ::
      (  N₃₁ <= 2147483647 / 4
        && 0 <= i₃₃
        && i₃₃ <= N₃₁
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> (exists i₇: int ::
                        i₇ < N₃₁
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃
                        && a₃₂[x₈] == 1)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃)
                || a₃₂[x₈] == a[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅
                        && b₃₄[x₁₂] == 1)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅)
                || b₃₄[x₁₂] == b[x₁₂])
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> i₁₁ < N₃₁))
        && 0 <= i₃₇
        && i₃₇ <= N₃₁
        && (forall x₁₆: int, i₁₅: int ::
              (  x₁₆ == i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> (exists i₁₅: int ::
                        i₁₅ < N₃₁
                        && x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇
                        && c₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || c₃₆[x₁₆] == c[x₁₆])
        && (forall i₁₅: int ::
              (  i₁₅ <= i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₂₀: int ::
              (x₂₀ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₂₀ == 0
                        && sum₃₈[x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])))
        && (forall x₂₀: int ::
                x₂₀ == 0
                || sum₃₈[x₂₀] == sum[0 := 0][x₂₀])
        && (forall i₁₉: int ::
              (  i₁₉ <= i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && 0 <= i₄₁
        && i₄₁ <= N₃₁
        && (forall x₂₄: int ::
              (x₂₄ == 0
                 ==> (exists i₂₃: int ::
                        i₂₃ < N₃₁
                        && x₂₄ == 0
                        && sum₄₀[x₂₄] == sum₃₈[0] + b₃₄[i₂₃])))
        && (forall x₂₄: int ::
                x₂₄ == 0
                || sum₄₀[x₂₄] == sum₃₈[x₂₄])
        && (forall i₂₃: int ::
              (  i₂₃ <= i₂₃
                && 0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> i₂₃ < N₃₁))
        && 0 <= i₄₃
        && i₄₃ <= N₃₁
        && (forall x₆₅₄: int ::
              (x₆₅₄ == 0
                 ==> (exists i₂₇: int ::
                        i₂₇ < N₃₁
                        && x₆₅₄ == 0
                        && sum₄₂[x₆₅₄] == sum₄₀[0] + c₃₆[i₂₇])))
        && (forall x₆₅₅: int ::
                x₆₅₅ == 0
                || sum₄₂[x₆₅₅] == sum₄₀[x₆₅₅])
        && (forall i₂₇: int ::
              (  i₂₇ <= i₂₇
                && 0 <= i₂₇
                && i₂₇ < i₄₃
                 ==> i₂₇ < N₃₁))
        && i₄₃ < N₃₁
        && x₂₈ == 0
         ==> i₄₁ < N₃₁
          || i₃₉ < N₃₁
          || i₃₇ < N₃₁
          || i₃₅ < N₃₁
          || i₃₃ < N₃₁
          || N₃₁ <= 0
          || (exists i₂₇: int ::
                  i₂₇ < N₃₁
                  && x₂₈ == 0
                  && sum₄₂[0 := sum₄₂[0] + c₃₆[i₄₃]][x₂₈] == sum₄₀[0] + c₃₆[i₂₇])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, b₃₄: [int]int, i₃₅: int, c₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, sum₄₀: [int]int, i₄₁: int, sum₄₂: [int]int, i₄₃: int ::
      (  N₃₁ <= 2147483647 / 4
        && 0 <= i₃₃
        && i₃₃ <= N₃₁
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> (exists i₇: int ::
                        i₇ < N₃₁
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃
                        && a₃₂[x₈] == 1)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₃₃)
                || a₃₂[x₈] == a[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅
                        && b₃₄[x₁₂] == 1)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₃₅)
                || b₃₄[x₁₂] == b[x₁₂])
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> i₁₁ < N₃₁))
        && 0 <= i₃₇
        && i₃₇ <= N₃₁
        && (forall x₁₆: int, i₁₅: int ::
              (  x₁₆ == i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> (exists i₁₅: int ::
                        i₁₅ < N₃₁
                        && x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇
                        && c₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || c₃₆[x₁₆] == c[x₁₆])
        && (forall i₁₅: int ::
              (  i₁₅ <= i₁₅
                && 0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₂₀: int ::
              (x₂₀ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₂₀ == 0
                        && sum₃₈[x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])))
        && (forall x₂₀: int ::
                x₂₀ == 0
                || sum₃₈[x₂₀] == sum[0 := 0][x₂₀])
        && (forall i₁₉: int ::
              (  i₁₉ <= i₁₉
                && 0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && 0 <= i₄₁
        && i₄₁ <= N₃₁
        && (forall x₂₄: int ::
              (x₂₄ == 0
                 ==> (exists i₂₃: int ::
                        i₂₃ < N₃₁
                        && x₂₄ == 0
                        && sum₄₀[x₂₄] == sum₃₈[0] + b₃₄[i₂₃])))
        && (forall x₂₄: int ::
                x₂₄ == 0
                || sum₄₀[x₂₄] == sum₃₈[x₂₄])
        && (forall i₂₃: int ::
              (  i₂₃ <= i₂₃
                && 0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> i₂₃ < N₃₁))
        && 0 <= i₄₃
        && i₄₃ <= N₃₁
        && (forall x₂₈: int ::
              (x₂₈ == 0
                 ==> (exists i₂₇: int ::
                        i₂₇ < N₃₁
                        && x₂₈ == 0
                        && sum₄₂[x₂₈] == sum₄₀[0] + c₃₆[i₂₇])))
        && (forall x₂₈: int ::
                x₂₈ == 0
                || sum₄₂[x₂₈] == sum₄₀[x₂₈])
        && (forall i₂₇: int ::
              (  i₂₇ <= i₂₇
                && 0 <= i₂₇
                && i₂₇ < i₄₃
                 ==> i₂₇ < N₃₁))
         ==> i₄₃ < N₃₁
          || i₄₁ < N₃₁
          || i₃₉ < N₃₁
          || i₃₇ < N₃₁
          || i₃₅ < N₃₁
          || i₃₃ < N₃₁
          || N₃₁ <= 0
          || sum₄₂[0] <= 3 * N₃₁));

