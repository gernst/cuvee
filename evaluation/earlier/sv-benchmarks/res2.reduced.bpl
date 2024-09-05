data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₃₁: int, sum: [int]int, a: [int]int, a₃₂: [int]int, i₃₃: int, x₁₂: int ::
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
              (  0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && x₁₂ == 0
         ==> i₃₃ < N₃₁
          || N₃₁ <= 0
          || (exists i₁₁: int ::
                  i₁₁ < N₃₁
                  && x₁₂ == 0
                  && sum[0 := 0][x₁₂] == sum[0 := 0][0] + a₃₂[i₁₁])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, a₃₂: [int]int, i₃₃: int, sum₃₄: [int]int, i₃₅: int, x₁₂: int ::
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
              (  0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₃₈: int ::
              (x₁₃₈ == 0
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₃₈ == 0
                        && sum₃₄[x₁₃₈] == sum[0 := 0][0] + a₃₂[i₁₁])))
        && (forall x₁₃₉: int ::
                x₁₃₉ == 0
                || sum₃₄[x₁₃₉] == sum[0 := 0][x₁₃₉])
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₃₅
                 ==> i₁₁ < N₃₁))
        && i₃₅ < N₃₁
        && x₁₂ == 0
         ==> i₃₃ < N₃₁
          || N₃₁ <= 0
          || (exists i₁₁: int ::
                  i₁₁ < N₃₁
                  && x₁₂ == 0
                  && sum₃₄[0 := sum₃₄[0] + a₃₂[i₃₅]][x₁₂] == sum[0 := 0][0] + a₃₂[i₁₁])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, a₃₂: [int]int, i₃₃: int, sum₃₄: [int]int, i₃₅: int, b₃₆: [int]int, i₃₇: int, x₂₀: int ::
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
              (  0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int ::
              (x₁₂ == 0
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == 0
                        && sum₃₄[x₁₂] == sum[0 := 0][0] + a₃₂[i₁₁])))
        && (forall x₁₂: int ::
                x₁₂ == 0
                || sum₃₄[x₁₂] == sum[0 := 0][x₁₂])
        && (forall i₁₁: int ::
              (  0 <= i₁₁
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
                        && b₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || b₃₆[x₁₆] == b[x₁₆])
        && (forall i₁₅: int ::
              (  0 <= i₁₅
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
                  && sum₃₄[x₂₀] == b₃₆[i₁₉] + sum₃₄[0])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, a₃₂: [int]int, i₃₃: int, sum₃₄: [int]int, i₃₅: int, b₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, x₂₀: int ::
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
              (  0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int ::
              (x₁₂ == 0
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == 0
                        && sum₃₄[x₁₂] == sum[0 := 0][0] + a₃₂[i₁₁])))
        && (forall x₁₂: int ::
                x₁₂ == 0
                || sum₃₄[x₁₂] == sum[0 := 0][x₁₂])
        && (forall i₁₁: int ::
              (  0 <= i₁₁
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
                        && b₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || b₃₆[x₁₆] == b[x₁₆])
        && (forall i₁₅: int ::
              (  0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₃₄₁: int ::
              (x₃₄₁ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₃₄₁ == 0
                        && sum₃₈[x₃₄₁] == b₃₆[i₁₉] + sum₃₄[0])))
        && (forall x₃₄₂: int ::
                x₃₄₂ == 0
                || sum₃₈[x₃₄₂] == sum₃₄[x₃₄₂])
        && (forall i₁₉: int ::
              (  0 <= i₁₉
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
                  && sum₃₈[0 := sum₃₈[0] + b₃₆[i₃₉]][x₂₀] == b₃₆[i₁₉] + sum₃₄[0])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, sum₃₄: [int]int, i₃₅: int, b₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, c₄₀: [int]int, i₄₁: int, x₂₈: int ::
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
              (  0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int ::
              (x₁₂ == 0
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == 0
                        && sum₃₄[x₁₂] == sum[0 := 0][0] + a₃₂[i₁₁])))
        && (forall x₁₂: int ::
                x₁₂ == 0
                || sum₃₄[x₁₂] == sum[0 := 0][x₁₂])
        && (forall i₁₁: int ::
              (  0 <= i₁₁
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
                        && b₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || b₃₆[x₁₆] == b[x₁₆])
        && (forall i₁₅: int ::
              (  0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₂₀: int ::
              (x₂₀ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₂₀ == 0
                        && sum₃₈[x₂₀] == b₃₆[i₁₉] + sum₃₄[0])))
        && (forall x₂₀: int ::
                x₂₀ == 0
                || sum₃₈[x₂₀] == sum₃₄[x₂₀])
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && 0 <= i₄₁
        && i₄₁ <= N₃₁
        && (forall x₂₄: int, i₂₃: int ::
              (  x₂₄ == i₂₃
                && 0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> (exists i₂₃: int ::
                        i₂₃ < N₃₁
                        && x₂₄ == i₂₃
                        && 0 <= i₂₃
                        && i₂₃ < i₄₁
                        && c₄₀[x₂₄] == 1)))
        && (forall x₂₄: int ::
                (exists i₂₃: int ::
                        x₂₄ == i₂₃
                        && 0 <= i₂₃
                        && i₂₃ < i₄₁)
                || c₄₀[x₂₄] == c[x₂₄])
        && (forall i₂₃: int ::
              (  0 <= i₂₃
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
                  && sum₃₈[x₂₈] == sum₃₈[0] + c₄₀[i₂₇])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, sum₃₄: [int]int, i₃₅: int, b₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, c₄₀: [int]int, i₄₁: int, sum₄₂: [int]int, i₄₃: int, x₂₈: int ::
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
              (  0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int ::
              (x₁₂ == 0
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == 0
                        && sum₃₄[x₁₂] == sum[0 := 0][0] + a₃₂[i₁₁])))
        && (forall x₁₂: int ::
                x₁₂ == 0
                || sum₃₄[x₁₂] == sum[0 := 0][x₁₂])
        && (forall i₁₁: int ::
              (  0 <= i₁₁
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
                        && b₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || b₃₆[x₁₆] == b[x₁₆])
        && (forall i₁₅: int ::
              (  0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₂₀: int ::
              (x₂₀ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₂₀ == 0
                        && sum₃₈[x₂₀] == b₃₆[i₁₉] + sum₃₄[0])))
        && (forall x₂₀: int ::
                x₂₀ == 0
                || sum₃₈[x₂₀] == sum₃₄[x₂₀])
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && 0 <= i₄₁
        && i₄₁ <= N₃₁
        && (forall x₂₄: int, i₂₃: int ::
              (  x₂₄ == i₂₃
                && 0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> (exists i₂₃: int ::
                        i₂₃ < N₃₁
                        && x₂₄ == i₂₃
                        && 0 <= i₂₃
                        && i₂₃ < i₄₁
                        && c₄₀[x₂₄] == 1)))
        && (forall x₂₄: int ::
                (exists i₂₃: int ::
                        x₂₄ == i₂₃
                        && 0 <= i₂₃
                        && i₂₃ < i₄₁)
                || c₄₀[x₂₄] == c[x₂₄])
        && (forall i₂₃: int ::
              (  0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> i₂₃ < N₃₁))
        && 0 <= i₄₃
        && i₄₃ <= N₃₁
        && (forall x₆₄₄: int ::
              (x₆₄₄ == 0
                 ==> (exists i₂₇: int ::
                        i₂₇ < N₃₁
                        && x₆₄₄ == 0
                        && sum₄₂[x₆₄₄] == sum₃₈[0] + c₄₀[i₂₇])))
        && (forall x₆₄₅: int ::
                x₆₄₅ == 0
                || sum₄₂[x₆₄₅] == sum₃₈[x₆₄₅])
        && (forall i₂₇: int ::
              (  0 <= i₂₇
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
                  && sum₄₂[0 := sum₄₂[0] + c₄₀[i₄₃]][x₂₈] == sum₃₈[0] + c₄₀[i₂₇])));

goal (forall N₃₁: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₃₂: [int]int, i₃₃: int, sum₃₄: [int]int, i₃₅: int, b₃₆: [int]int, i₃₇: int, sum₃₈: [int]int, i₃₉: int, c₄₀: [int]int, i₄₁: int, sum₄₂: [int]int, i₄₃: int ::
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
              (  0 <= i₇
                && i₇ < i₃₃
                 ==> i₇ < N₃₁))
        && 0 <= i₃₅
        && i₃₅ <= N₃₁
        && (forall x₁₂: int ::
              (x₁₂ == 0
                 ==> (exists i₁₁: int ::
                        i₁₁ < N₃₁
                        && x₁₂ == 0
                        && sum₃₄[x₁₂] == sum[0 := 0][0] + a₃₂[i₁₁])))
        && (forall x₁₂: int ::
                x₁₂ == 0
                || sum₃₄[x₁₂] == sum[0 := 0][x₁₂])
        && (forall i₁₁: int ::
              (  0 <= i₁₁
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
                        && b₃₆[x₁₆] == 1)))
        && (forall x₁₆: int ::
                (exists i₁₅: int ::
                        x₁₆ == i₁₅
                        && 0 <= i₁₅
                        && i₁₅ < i₃₇)
                || b₃₆[x₁₆] == b[x₁₆])
        && (forall i₁₅: int ::
              (  0 <= i₁₅
                && i₁₅ < i₃₇
                 ==> i₁₅ < N₃₁))
        && 0 <= i₃₉
        && i₃₉ <= N₃₁
        && (forall x₂₀: int ::
              (x₂₀ == 0
                 ==> (exists i₁₉: int ::
                        i₁₉ < N₃₁
                        && x₂₀ == 0
                        && sum₃₈[x₂₀] == b₃₆[i₁₉] + sum₃₄[0])))
        && (forall x₂₀: int ::
                x₂₀ == 0
                || sum₃₈[x₂₀] == sum₃₄[x₂₀])
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₃₉
                 ==> i₁₉ < N₃₁))
        && 0 <= i₄₁
        && i₄₁ <= N₃₁
        && (forall x₂₄: int, i₂₃: int ::
              (  x₂₄ == i₂₃
                && 0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> (exists i₂₃: int ::
                        i₂₃ < N₃₁
                        && x₂₄ == i₂₃
                        && 0 <= i₂₃
                        && i₂₃ < i₄₁
                        && c₄₀[x₂₄] == 1)))
        && (forall x₂₄: int ::
                (exists i₂₃: int ::
                        x₂₄ == i₂₃
                        && 0 <= i₂₃
                        && i₂₃ < i₄₁)
                || c₄₀[x₂₄] == c[x₂₄])
        && (forall i₂₃: int ::
              (  0 <= i₂₃
                && i₂₃ < i₄₁
                 ==> i₂₃ < N₃₁))
        && 0 <= i₄₃
        && i₄₃ <= N₃₁
        && (forall x₂₈: int ::
              (x₂₈ == 0
                 ==> (exists i₂₇: int ::
                        i₂₇ < N₃₁
                        && x₂₈ == 0
                        && sum₄₂[x₂₈] == sum₃₈[0] + c₄₀[i₂₇])))
        && (forall x₂₈: int ::
                x₂₈ == 0
                || sum₄₂[x₂₈] == sum₃₈[x₂₈])
        && (forall i₂₇: int ::
              (  0 <= i₂₇
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

