data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₃: int, b: [int]int, b₁₄: [int]int, i₁₅: int, i₅: int ::
      (  -2147483648 <= N₁₃
        && N₁₃ < 2147483648
        && N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅₈: int ::
              (  0 <= i₅₈
                && i₅₈ < i₁₅
                 ==> i₅₈ == 0
                    && i₅₈ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₅₈ == 0
                       ==> false)
                    && i₅₈ < N₁₃
                    && b₁₄[i₅₈] == 2 + b[-1 + i₅₈]))
        && (forall i₅₉: int ::
                  0 <= i₅₉
                  && i₅₉ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₅₉] == b[i₅₉])
        && i₁₅ < N₁₃
        && i₁₅ == 0
         ==> 0 <= i₅
          || N₁₃ <= 0
          || b₁₄[0 := 1][0] == b[0]));

goal {:named "invariant forward"} (forall N₁₃: int, b: [int]int, b₁₄: [int]int, i₁₅: int, i₅: int ::
      (  -2147483648 <= N₁₃
        && N₁₃ < 2147483648
        && N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₇₀: int ::
              (  0 <= i₇₀
                && i₇₀ < i₁₅
                 ==> i₇₀ == 0
                    && i₇₀ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₇₀ == 0
                       ==> false)
                    && i₇₀ < N₁₃
                    && b₁₄[i₇₀] == 2 + b[-1 + i₇₀]))
        && (forall i₇₁: int ::
                  0 <= i₇₁
                  && i₇₁ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₇₁] == b[i₇₁])
        && i₁₅ < N₁₃
        && i₁₅ == 0
         ==> i₅ < i₁₅ + 1
          || N₁₃ <= 0
          || b₁₄[0 := 1][0] == b[0]));

goal {:named "invariant forward"} (forall N₁₃: int, b: [int]int, b₁₄: [int]int, i₁₅: int, i₅: int ::
      (  -2147483648 <= N₁₃
        && N₁₃ < 2147483648
        && N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₈₆: int ::
              (  0 <= i₈₆
                && i₈₆ < i₁₅
                 ==> i₈₆ == 0
                    && i₈₆ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₈₆ == 0
                       ==> false)
                    && i₈₆ < N₁₃
                    && b₁₄[i₈₆] == 2 + b[-1 + i₈₆]))
        && (forall i₈₇: int ::
                  0 <= i₈₇
                  && i₈₇ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₈₇] == b[i₈₇])
        && i₁₅ < N₁₃
        && 0 <= i₅
        && i₅ < i₁₅ + 1
         ==> i₁₅ == 0
          || N₁₃ <= 0
          ||   i₅ == 0
            && i₅ < N₁₃
            && b₁₄[i₁₅ := b₁₄[i₁₅ - 1] + 2][0] == 1
          ||   (i₅ == 0
               ==> false)
            && i₅ < N₁₃
            && b₁₄[i₁₅ := b₁₄[i₁₅ - 1] + 2][i₅] == 2 + b[-1 + i₅]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₈: int ::
      (  -2147483648 <= N₁₃
        && N₁₃ < 2147483648
        && N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && b₁₄[i₅] == 2 + b[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₅] == b[i₅])
        && 0 <= i₁₇
        && (forall i₁₆₅: int ::
              (  0 <= i₁₆₅
                && i₁₆₅ < i₁₇
                 ==> i₁₆₅ == 0
                    && i₁₆₅ < N₁₃
                    && a₁₆[0] == 1 + N₁₃
                  ||   (i₁₆₅ == 0
                       ==> false)
                    && i₁₆₅ < N₁₃
                    && a₁₆[i₁₆₅] == 2 + a[-1 + i₁₆₅] + b₁₄[-1 + i₁₆₅]))
        && (forall i₁₆₆: int ::
                  0 <= i₁₆₆
                  && i₁₆₆ < i₁₇
                ||   a₁₆[0] == a[0]
                  && a₁₆[i₁₆₆] == a[i₁₆₆])
        && i₁₇ < N₁₃
        && i₁₇ == 0
         ==> 0 <= i₈
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || a₁₆[0 := N₁₃ + 1][0] == a[0]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₈: int ::
      (  -2147483648 <= N₁₃
        && N₁₃ < 2147483648
        && N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && b₁₄[i₅] == 2 + b[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₅] == b[i₅])
        && 0 <= i₁₇
        && (forall i₁₈₃: int ::
              (  0 <= i₁₈₃
                && i₁₈₃ < i₁₇
                 ==> i₁₈₃ == 0
                    && i₁₈₃ < N₁₃
                    && a₁₆[0] == 1 + N₁₃
                  ||   (i₁₈₃ == 0
                       ==> false)
                    && i₁₈₃ < N₁₃
                    && a₁₆[i₁₈₃] == 2 + a[-1 + i₁₈₃] + b₁₄[-1 + i₁₈₃]))
        && (forall i₁₈₄: int ::
                  0 <= i₁₈₄
                  && i₁₈₄ < i₁₇
                ||   a₁₆[0] == a[0]
                  && a₁₆[i₁₈₄] == a[i₁₈₄])
        && i₁₇ < N₁₃
        && i₁₇ == 0
         ==> i₈ < i₁₇ + 1
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || a₁₆[0 := N₁₃ + 1][0] == a[0]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₈: int ::
      (  -2147483648 <= N₁₃
        && N₁₃ < 2147483648
        && N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && b₁₄[i₅] == 2 + b[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₅] == b[i₅])
        && 0 <= i₁₇
        && (forall i₂₀₈: int ::
              (  0 <= i₂₀₈
                && i₂₀₈ < i₁₇
                 ==> i₂₀₈ == 0
                    && i₂₀₈ < N₁₃
                    && a₁₆[0] == 1 + N₁₃
                  ||   (i₂₀₈ == 0
                       ==> false)
                    && i₂₀₈ < N₁₃
                    && a₁₆[i₂₀₈] == 2 + a[-1 + i₂₀₈] + b₁₄[-1 + i₂₀₈]))
        && (forall i₂₀₉: int ::
                  0 <= i₂₀₉
                  && i₂₀₉ < i₁₇
                ||   a₁₆[0] == a[0]
                  && a₁₆[i₂₀₉] == a[i₂₀₉])
        && i₁₇ < N₁₃
        && 0 <= i₈
        && i₈ < i₁₇ + 1
         ==> i₁₇ == 0
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          ||   i₈ == 0
            && i₈ < N₁₃
            && a₁₆[i₁₇ := a₁₆[i₁₇ - 1] + b₁₄[i₁₇ - 1] + 2][0] == 1 + N₁₃
          ||   (i₈ == 0
               ==> false)
            && i₈ < N₁₃
            && a₁₆[i₁₇ := a₁₆[i₁₇ - 1] + b₁₄[i₁₇ - 1] + 2][i₈] == 2 + a[-1 + i₈] + b₁₄[-1 + i₈]));

goal {:named "assert"} (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  -2147483648 <= N₁₃
        && N₁₃ < 2147483648
        && N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && b₁₄[i₅] == 2 + b[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₅] == b[i₅])
        && 0 <= i₁₇
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₇
                 ==> i₈ == 0
                    && i₈ < N₁₃
                    && a₁₆[0] == 1 + N₁₃
                  ||   (i₈ == 0
                       ==> false)
                    && i₈ < N₁₃
                    && a₁₆[i₈] == 2 + a[-1 + i₈] + b₁₄[-1 + i₈]))
        && (forall i₈: int ::
                  0 <= i₈
                  && i₈ < i₁₇
                ||   a₁₆[0] == a[0]
                  && a₁₆[i₈] == a[i₈])
        && 0 <= i₁₈
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₁₈
                 ==> i₁₁ < N₁₃))
        && i₁₈ < N₁₃
         ==> i₁₇ < N₁₃
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || a₁₆[i₁₈] == N₁₃ + (i₁₈ + 1) * (i₁₈ + 1)));

