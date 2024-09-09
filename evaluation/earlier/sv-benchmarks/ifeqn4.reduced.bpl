data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₁₁₈: int ::
              (  0 <= i₁₁₈
                && i₁₁₈ < i₁₅
                 ==> i₁₁₈ == 0
                    && i₁₁₈ < N₁₃
                    && a₁₄[0] == 8
                  ||   (i₁₁₈ == 0
                       ==> false)
                    && i₁₁₈ < N₁₃
                    && a₁₄[i₁₁₈] == 8 + a[-1 + i₁₁₈]))
        && (forall i₁₁₉: int ::
                  0 <= i₁₁₉
                  && i₁₁₉ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₁₁₉] == a[i₁₁₉])
        && i₁₅ < N₁₃
        && i₁₅ == 0
         ==> 0 <= i₅
          || N₁₃ <= 0
          || a₁₄[0 := 8][0] == a[0]));

goal (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₁₃₀: int ::
              (  0 <= i₁₃₀
                && i₁₃₀ < i₁₅
                 ==> i₁₃₀ == 0
                    && i₁₃₀ < N₁₃
                    && a₁₄[0] == 8
                  ||   (i₁₃₀ == 0
                       ==> false)
                    && i₁₃₀ < N₁₃
                    && a₁₄[i₁₃₀] == 8 + a[-1 + i₁₃₀]))
        && (forall i₁₃₁: int ::
                  0 <= i₁₃₁
                  && i₁₃₁ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₁₃₁] == a[i₁₃₁])
        && i₁₅ < N₁₃
        && i₁₅ == 0
         ==> i₅ < i₁₅ + 1
          || N₁₃ <= 0
          || a₁₄[0 := 8][0] == a[0]));

goal (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₁₅₆: int ::
              (  0 <= i₁₅₆
                && i₁₅₆ < i₁₅
                 ==> i₁₅₆ == 0
                    && i₁₅₆ < N₁₃
                    && a₁₄[0] == 8
                  ||   (i₁₅₆ == 0
                       ==> false)
                    && i₁₅₆ < N₁₃
                    && a₁₄[i₁₅₆] == 8 + a[-1 + i₁₅₆]))
        && (forall i₁₅₇: int ::
                  0 <= i₁₅₇
                  && i₁₅₇ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₁₅₇] == a[i₁₅₇])
        && i₁₅ < N₁₃
        && 0 <= i₅
        && i₅ < i₁₅ + 1
         ==> i₁₅ == 0
          || N₁₃ <= 0
          || i₅ == 0
          || a₁₄[i₁₅ := a₁₄[i₁₅ - 1] + 8][i₅] == 8 + a[-1 + i₅]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && a₁₄[0] == 8
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && a₁₄[i₅] == 8 + a[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₅] == a[i₅])
        && 0 <= i₁₇
        && (forall i₃₇₃: int ::
              (  0 <= i₃₇₃
                && i₃₇₃ < i₁₇
                 ==> i₃₇₃ == 0
                    && i₃₇₃ < N₁₃
                    && b₁₆[0] == 1
                  ||   (i₃₇₃ == 0
                       ==> false)
                    && i₃₇₃ < N₁₃
                    && b₁₆[i₃₇₃] == b[-1 + i₃₇₃] + a₁₄[-1 + i₃₇₃]))
        && (forall i₃₇₄: int ::
                  0 <= i₃₇₄
                  && i₃₇₄ < i₁₇
                ||   b₁₆[0] == b[0]
                  && b₁₆[i₃₇₄] == b[i₃₇₄])
        && i₁₇ < N₁₃
        && i₁₇ == 0
         ==> 0 <= i₈
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[0 := 1][0] == b[0]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && a₁₄[0] == 8
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && a₁₄[i₅] == 8 + a[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₅] == a[i₅])
        && 0 <= i₁₇
        && (forall i₃₉₁: int ::
              (  0 <= i₃₉₁
                && i₃₉₁ < i₁₇
                 ==> i₃₉₁ == 0
                    && i₃₉₁ < N₁₃
                    && b₁₆[0] == 1
                  ||   (i₃₉₁ == 0
                       ==> false)
                    && i₃₉₁ < N₁₃
                    && b₁₆[i₃₉₁] == b[-1 + i₃₉₁] + a₁₄[-1 + i₃₉₁]))
        && (forall i₃₉₂: int ::
                  0 <= i₃₉₂
                  && i₃₉₂ < i₁₇
                ||   b₁₆[0] == b[0]
                  && b₁₆[i₃₉₂] == b[i₃₉₂])
        && i₁₇ < N₁₃
        && i₁₇ == 0
         ==> i₈ < i₁₇ + 1
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[0 := 1][0] == b[0]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ == 0
                    && i₅ < N₁₃
                    && a₁₄[0] == 8
                  ||   (i₅ == 0
                       ==> false)
                    && i₅ < N₁₃
                    && a₁₄[i₅] == 8 + a[-1 + i₅]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₅
                ||   a₁₄[0] == a[0]
                  && a₁₄[i₅] == a[i₅])
        && 0 <= i₁₇
        && (forall i₄₃₂: int ::
              (  0 <= i₄₃₂
                && i₄₃₂ < i₁₇
                 ==> i₄₃₂ == 0
                    && i₄₃₂ < N₁₃
                    && b₁₆[0] == 1
                  ||   (i₄₃₂ == 0
                       ==> false)
                    && i₄₃₂ < N₁₃
                    && b₁₆[i₄₃₂] == b[-1 + i₄₃₂] + a₁₄[-1 + i₄₃₂]))
        && (forall i₄₃₃: int ::
                  0 <= i₄₃₃
                  && i₄₃₃ < i₁₇
                ||   b₁₆[0] == b[0]
                  && b₁₆[i₄₃₃] == b[i₄₃₃])
        && i₁₇ < N₁₃
        && 0 <= i₈
        && i₈ < i₁₇ + 1
         ==> i₁₇ == 0
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || i₈ == 0
          || b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + a₁₄[i₁₇ - 1]][i₈] == b[-1 + i₈] + a₁₄[-1 + i₈]));

