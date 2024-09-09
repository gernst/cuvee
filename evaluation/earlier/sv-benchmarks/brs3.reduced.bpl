data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 3 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 3
                  ||   (i₅ % 3 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₁₇: int ::
              (  0 <= i₁₁₇
                && i₁₁₇ < i₁₅
                 ==> i₁₁₇ == 0
                    && i₁₁₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₁₇ == 0
                       ==> false)
                    && i₁₁₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₁₇] + sum[0]))
        && (forall i₁₁₈: int ::
                  0 <= i₁₁₈
                  && i₁₁₈ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && i₁₅ == 0
         ==> 0 <= i₈
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := 0][0] == sum[0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 3 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 3
                  ||   (i₅ % 3 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₂₇: int ::
              (  0 <= i₁₂₇
                && i₁₂₇ < i₁₅
                 ==> i₁₂₇ == 0
                    && i₁₂₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₂₇ == 0
                       ==> false)
                    && i₁₂₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₂₇] + sum[0]))
        && (forall i₁₂₈: int ::
                  0 <= i₁₂₈
                  && i₁₂₈ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && i₁₅ == 0
         ==> i₈ < i₁₅ + 1
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := 0][0] == sum[0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 3 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 3
                  ||   (i₅ % 3 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₄₄: int ::
              (  0 <= i₁₄₄
                && i₁₄₄ < i₁₅
                 ==> i₁₄₄ == 0
                    && i₁₄₄ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₄₄ == 0
                       ==> false)
                    && i₁₄₄ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₄₄] + sum[0]))
        && (forall i₁₄₅: int ::
                  0 <= i₁₄₅
                  && i₁₄₅ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && 0 <= i₈
        && i₈ < i₁₅ + 1
         ==> i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          ||   i₈ == 0
            && i₈ < N₁₁
            && sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == 0
          ||   (i₈ == 0
               ==> false)
            && i₈ < N₁₁
            && sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == a₁₂[i₈] + sum[0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 3 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 3
                  ||   (i₅ % 3 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₅₄: int ::
              (  0 <= i₁₅₄
                && i₁₅₄ < i₁₅
                 ==> i₁₅₄ == 0
                    && i₁₅₄ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₅₄ == 0
                       ==> false)
                    && i₁₅₄ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₅₄] + sum[0]))
        && (forall i₁₅₅: int ::
                  0 <= i₁₅₅
                  && i₁₅₅ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> 0 <= i₈
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 3 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 3
                  ||   (i₅ % 3 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₆₄: int ::
              (  0 <= i₁₆₄
                && i₁₆₄ < i₁₅
                 ==> i₁₆₄ == 0
                    && i₁₆₄ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₆₄ == 0
                       ==> false)
                    && i₁₆₄ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₆₄] + sum[0]))
        && (forall i₁₆₅: int ::
                  0 <= i₁₆₅
                  && i₁₆₅ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> i₈ < i₁₅ + 1
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));

