data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₅: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₂₆: [int]int, i₂₇: int, b₂₈: [int]int, i₂₉: int, c₃₀: [int]int, i₃₁: int, sum₃₂: [int]int, i₃₃: int, i₁₆: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < N₂₅
                  && a₂₆[i₇] == 1))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₇
                || a₂₆[i₇] == a[i₇])
        && 0 <= i₂₉
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₉
                 ==> i₁₀ < N₂₅
                  && b₂₈[i₁₀] == 1))
        && (forall i₁₀: int ::
                  0 <= i₁₀
                  && i₁₀ < i₂₉
                || b₂₈[i₁₀] == b[i₁₀])
        && 0 <= i₃₁
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> i₁₃ < N₂₅
                  && c₃₀[i₁₃] == 1))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₃₁
                || c₃₀[i₁₃] == c[i₁₃])
        && 0 <= i₃₃
        && (forall i₃₆₀: int ::
              (  0 <= i₃₆₀
                && i₃₆₀ < i₃₃
                 ==> i₃₆₀ < N₂₅
                  && sum₃₂[0] == a₂₆[i₃₆₀] + sum[0 := 0][0]))
        && (forall i₃₆₁: int ::
                  0 <= i₃₆₁
                  && i₃₆₁ < i₃₃
                || sum₃₂[0] == sum[0 := 0][0])
        && i₃₃ < N₂₅
         ==> 0 <= i₁₆
          || i₃₁ < N₂₅
          || i₂₉ < N₂₅
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₃₂[0 := sum₃₂[0] + a₂₆[i₃₃]][0] == sum[0 := 0][0]));

goal (forall N₂₅: int, sum: [int]int, a: [int]int, b: [int]int, c: [int]int, a₂₆: [int]int, i₂₇: int, b₂₈: [int]int, i₂₉: int, c₃₀: [int]int, i₃₁: int, sum₃₂: [int]int, i₃₃: int, i₁₆: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < N₂₅
                  && a₂₆[i₇] == 1))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₇
                || a₂₆[i₇] == a[i₇])
        && 0 <= i₂₉
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₉
                 ==> i₁₀ < N₂₅
                  && b₂₈[i₁₀] == 1))
        && (forall i₁₀: int ::
                  0 <= i₁₀
                  && i₁₀ < i₂₉
                || b₂₈[i₁₀] == b[i₁₀])
        && 0 <= i₃₁
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> i₁₃ < N₂₅
                  && c₃₀[i₁₃] == 1))
        && (forall i₁₃: int ::
                  0 <= i₁₃
                  && i₁₃ < i₃₁
                || c₃₀[i₁₃] == c[i₁₃])
        && 0 <= i₃₃
        && (forall i₃₇₆: int ::
              (  0 <= i₃₇₆
                && i₃₇₆ < i₃₃
                 ==> i₃₇₆ < N₂₅
                  && sum₃₂[0] == a₂₆[i₃₇₆] + sum[0 := 0][0]))
        && (forall i₃₇₇: int ::
                  0 <= i₃₇₇
                  && i₃₇₇ < i₃₃
                || sum₃₂[0] == sum[0 := 0][0])
        && i₃₃ < N₂₅
         ==> i₁₆ < i₃₃ + 1
          || i₃₁ < N₂₅
          || i₂₉ < N₂₅
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₃₂[0 := sum₃₂[0] + a₂₆[i₃₃]][0] == sum[0 := 0][0]));

