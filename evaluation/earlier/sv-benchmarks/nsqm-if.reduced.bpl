data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, b: [int]int, b₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₁₁₈: int ::
              (  0 <= i₁₁₈
                && i₁₁₈ < i₁₅
                 ==> i₁₁₈ == 0
                    && i₁₁₈ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₁₁₈ == 0
                       ==> false)
                    && i₁₁₈ < N₁₃
                    && b₁₄[i₁₁₈] == 2 + b[-1 + i₁₁₈]))
        && (forall i₁₁₉: int ::
                  0 <= i₁₁₉
                  && i₁₁₉ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₁₁₉] == b[i₁₁₉])
        && i₁₅ < N₁₃
        && i₁₅ == 0
         ==> 0 <= i₅
          || N₁₃ <= 0
          || b₁₄[0 := 1][0] == b[0]));

goal (forall N₁₃: int, b: [int]int, b₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₁₃₀: int ::
              (  0 <= i₁₃₀
                && i₁₃₀ < i₁₅
                 ==> i₁₃₀ == 0
                    && i₁₃₀ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₁₃₀ == 0
                       ==> false)
                    && i₁₃₀ < N₁₃
                    && b₁₄[i₁₃₀] == 2 + b[-1 + i₁₃₀]))
        && (forall i₁₃₁: int ::
                  0 <= i₁₃₁
                  && i₁₃₁ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₁₃₁] == b[i₁₃₁])
        && i₁₅ < N₁₃
        && i₁₅ == 0
         ==> i₅ < i₁₅ + 1
          || N₁₃ <= 0
          || b₁₄[0 := 1][0] == b[0]));

goal (forall N₁₃: int, b: [int]int, b₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₁₅₆: int ::
              (  0 <= i₁₅₆
                && i₁₅₆ < i₁₅
                 ==> i₁₅₆ == 0
                    && i₁₅₆ < N₁₃
                    && b₁₄[0] == 1
                  ||   (i₁₅₆ == 0
                       ==> false)
                    && i₁₅₆ < N₁₃
                    && b₁₄[i₁₅₆] == 2 + b[-1 + i₁₅₆]))
        && (forall i₁₅₇: int ::
                  0 <= i₁₅₇
                  && i₁₅₇ < i₁₅
                ||   b₁₄[0] == b[0]
                  && b₁₄[i₁₅₇] == b[i₁₅₇])
        && i₁₅ < N₁₃
        && 0 <= i₅
        && i₅ < i₁₅ + 1
         ==> i₁₅ == 0
          || N₁₃ <= 0
          || i₅ == 0
          || b₁₄[i₁₅ := b₁₄[i₁₅ - 1] + 2][i₅] == 2 + b[-1 + i₅]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
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
        && (forall i₃₇₃: int ::
              (  0 <= i₃₇₃
                && i₃₇₃ < i₁₇
                 ==> i₃₇₃ == 0
                    && i₃₇₃ < N₁₃
                    && a₁₆[0] == 1 + N₁₃
                  ||   (i₃₇₃ == 0
                       ==> false)
                    && i₃₇₃ < N₁₃
                    && a₁₆[i₃₇₃] == 2 + a[-1 + i₃₇₃] + b₁₄[-1 + i₃₇₃]))
        && (forall i₃₇₄: int ::
                  0 <= i₃₇₄
                  && i₃₇₄ < i₁₇
                ||   a₁₆[0] == a[0]
                  && a₁₆[i₃₇₄] == a[i₃₇₄])
        && i₁₇ < N₁₃
        && i₁₇ == 0
         ==> 0 <= i₈
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || a₁₆[0 := N₁₃ + 1][0] == a[0]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
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
        && (forall i₃₉₁: int ::
              (  0 <= i₃₉₁
                && i₃₉₁ < i₁₇
                 ==> i₃₉₁ == 0
                    && i₃₉₁ < N₁₃
                    && a₁₆[0] == 1 + N₁₃
                  ||   (i₃₉₁ == 0
                       ==> false)
                    && i₃₉₁ < N₁₃
                    && a₁₆[i₃₉₁] == 2 + a[-1 + i₃₉₁] + b₁₄[-1 + i₃₉₁]))
        && (forall i₃₉₂: int ::
                  0 <= i₃₉₂
                  && i₃₉₂ < i₁₇
                ||   a₁₆[0] == a[0]
                  && a₁₆[i₃₉₂] == a[i₃₉₂])
        && i₁₇ < N₁₃
        && i₁₇ == 0
         ==> i₈ < i₁₇ + 1
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || a₁₆[0 := N₁₃ + 1][0] == a[0]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
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
        && (forall i₄₃₂: int ::
              (  0 <= i₄₃₂
                && i₄₃₂ < i₁₇
                 ==> i₄₃₂ == 0
                    && i₄₃₂ < N₁₃
                    && a₁₆[0] == 1 + N₁₃
                  ||   (i₄₃₂ == 0
                       ==> false)
                    && i₄₃₂ < N₁₃
                    && a₁₆[i₄₃₂] == 2 + a[-1 + i₄₃₂] + b₁₄[-1 + i₄₃₂]))
        && (forall i₄₃₃: int ::
                  0 <= i₄₃₃
                  && i₄₃₃ < i₁₇
                ||   a₁₆[0] == a[0]
                  && a₁₆[i₄₃₃] == a[i₄₃₃])
        && i₁₇ < N₁₃
        && 0 <= i₈
        && i₈ < i₁₇ + 1
         ==> i₁₇ == 0
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || i₈ == 0
          || a₁₆[i₁₇ := a₁₆[i₁₇ - 1] + b₁₄[i₁₇ - 1] + 2][i₈] == 2 + a[-1 + i₈] + b₁₄[-1 + i₈]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  N₁₃ <= 2147483647 / 4
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

