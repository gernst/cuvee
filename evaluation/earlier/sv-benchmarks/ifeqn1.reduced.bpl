data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅₈: int ::
              (  0 <= i₅₈
                && i₅₈ < i₁₅
                 ==> i₅₈ == 0
                    && i₅₈ < N₁₃
                    && a₁₄[0] == 2
                  ||   (i₅₈ == 0
                       ==> false)
                    && i₅₈ < N₁₃
                    && a₁₄[i₅₈] == 2 + a[-1 + i₅₈]))
        && (forall i₅₉: int ::
                  0 <= i₅₉
                  && i₅₉ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₅₉] == a[i₅₉])
        && i₁₅ < N₁₃
        && i₁₅ == 0
         ==> 0 <= i₅
          || N₁₃ <= 0
          || a₁₄[0 := 2][0] == a[0]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₇₀: int ::
              (  0 <= i₇₀
                && i₇₀ < i₁₅
                 ==> i₇₀ == 0
                    && i₇₀ < N₁₃
                    && a₁₄[0] == 2
                  ||   (i₇₀ == 0
                       ==> false)
                    && i₇₀ < N₁₃
                    && a₁₄[i₇₀] == 2 + a[-1 + i₇₀]))
        && (forall i₇₁: int ::
                  0 <= i₇₁
                  && i₇₁ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₇₁] == a[i₇₁])
        && i₁₅ < N₁₃
        && i₁₅ == 0
         ==> i₅ < i₁₅ + 1
          || N₁₃ <= 0
          || a₁₄[0 := 2][0] == a[0]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₈₆: int ::
              (  0 <= i₈₆
                && i₈₆ < i₁₅
                 ==> i₈₆ == 0
                    && i₈₆ < N₁₃
                    && a₁₄[0] == 2
                  ||   (i₈₆ == 0
                       ==> false)
                    && i₈₆ < N₁₃
                    && a₁₄[i₈₆] == 2 + a[-1 + i₈₆]))
        && (forall i₈₇: int ::
                  0 <= i₈₇
                  && i₈₇ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₈₇] == a[i₈₇])
        && i₁₅ < N₁₃
        && 0 <= i₅
        && i₅ < i₁₅ + 1
         ==> i₁₅ == 0
          || N₁₃ <= 0
          ||   i₅ == 0
            && i₅ < N₁₃
            && a₁₄[i₁₅ := a₁₄[i₁₅ - 1] + 2][0] == 2
          ||   (i₅ == 0
               ==> false)
            && i₅ < N₁₃
            && a₁₄[i₁₅ := a₁₄[i₁₅ - 1] + 2][i₅] == 2 + a[-1 + i₅]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && a₁₄[0] == 2
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && a₁₄[i₅] == 2 + a[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₅] == a[i₅])
        && 0 <= i₁₇
        && (forall i₁₆₅: int ::
              (  0 <= i₁₆₅
                && i₁₆₅ < i₁₇
                 ==> i₁₆₅ == 0
                    && i₁₆₅ < N₁₃
                    && b₁₆[0] == 1
                  ||   (i₁₆₅ == 0
                       ==> false)
                    && i₁₆₅ < N₁₃
                    && b₁₆[i₁₆₅] == b[-1 + i₁₆₅] + a₁₄[-1 + i₁₆₅]))
        && (forall i₁₆₆: int ::
                  0 <= i₁₆₆
                  && i₁₆₆ < i₁₇
                ||   b₁₆[0] == b[0]
                  && b₁₆[i₁₆₆] == b[i₁₆₆])
        && i₁₇ < N₁₃
        && i₁₇ == 0
         ==> 0 <= i₈
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[0 := 1][0] == b[0]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && a₁₄[0] == 2
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && a₁₄[i₅] == 2 + a[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₅] == a[i₅])
        && 0 <= i₁₇
        && (forall i₁₈₃: int ::
              (  0 <= i₁₈₃
                && i₁₈₃ < i₁₇
                 ==> i₁₈₃ == 0
                    && i₁₈₃ < N₁₃
                    && b₁₆[0] == 1
                  ||   (i₁₈₃ == 0
                       ==> false)
                    && i₁₈₃ < N₁₃
                    && b₁₆[i₁₈₃] == b[-1 + i₁₈₃] + a₁₄[-1 + i₁₈₃]))
        && (forall i₁₈₄: int ::
                  0 <= i₁₈₄
                  && i₁₈₄ < i₁₇
                ||   b₁₆[0] == b[0]
                  && b₁₆[i₁₈₄] == b[i₁₈₄])
        && i₁₇ < N₁₃
        && i₁₇ == 0
         ==> i₈ < i₁₇ + 1
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[0 := 1][0] == b[0]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && a₁₄[0] == 2
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && a₁₄[i₅] == 2 + a[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₅] == a[i₅])
        && 0 <= i₁₇
        && (forall i₂₀₈: int ::
              (  0 <= i₂₀₈
                && i₂₀₈ < i₁₇
                 ==> i₂₀₈ == 0
                    && i₂₀₈ < N₁₃
                    && b₁₆[0] == 1
                  ||   (i₂₀₈ == 0
                       ==> false)
                    && i₂₀₈ < N₁₃
                    && b₁₆[i₂₀₈] == b[-1 + i₂₀₈] + a₁₄[-1 + i₂₀₈]))
        && (forall i₂₀₉: int ::
                  0 <= i₂₀₉
                  && i₂₀₉ < i₁₇
                ||   b₁₆[0] == b[0]
                  && b₁₆[i₂₀₉] == b[i₂₀₉])
        && i₁₇ < N₁₃
        && 0 <= i₈
        && i₈ < i₁₇ + 1
         ==> i₁₇ == 0
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          ||   i₈ == 0
            && i₈ < N₁₃
            && b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + a₁₄[i₁₇ - 1]][0] == 1
          ||   (i₈ == 0
               ==> false)
            && i₈ < N₁₃
            && b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + a₁₄[i₁₇ - 1]][i₈] == b[-1 + i₈] + a₁₄[-1 + i₈]));

goal {:named "assert"} (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && a₁₄[0] == 2
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && a₁₄[i₅] == 2 + a[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₅] == a[i₅])
        && 0 <= i₁₇
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₇
                 ==> i₈ == 0
                    && i₈ < N₁₃
                    && b₁₆[0] == 1
                  ||   (i₈ == 0
                       ==> false)
                    && i₈ < N₁₃
                    && b₁₆[i₈] == b[-1 + i₈] + a₁₄[-1 + i₈]))
        && (forall i₈: int ::
                  0 <= i₈
                  && i₈ < i₁₇
                ||   b₁₆[0] == b[0]
                  && b₁₆[i₈] == b[i₈])
        && 0 <= i₁₈
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₁₈
                 ==> i₁₁ < N₁₃))
        && i₁₈ < N₁₃
         ==> i₁₇ < N₁₃
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[i₁₈] == i₁₈ * i₁₈ + i₁₈ + 1));

