data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, a₁₈: [int]int, i₁₉: int, i₆: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₆₈: int ::
              (  0 <= i₆₈
                && i₆₈ < i₁₉
                 ==> i₆₈ == 0
                    && i₆₈ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₆₈ == 0
                       ==> false)
                    && i₆₈ < N₁₇
                    && a₁₈[i₆₈] == 6 + a[-1 + i₆₈]))
        && (forall i₆₉: int ::
                  0 <= i₆₉
                  && i₆₉ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₆₉] == a[i₆₉])
        && i₁₉ < N₁₇
        && i₁₉ == 0
         ==> 0 <= i₆
          || N₁₇ <= 0
          || a₁₈[0 := 6][0] == a[0]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, a₁₈: [int]int, i₁₉: int, i₆: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₈₀: int ::
              (  0 <= i₈₀
                && i₈₀ < i₁₉
                 ==> i₈₀ == 0
                    && i₈₀ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₈₀ == 0
                       ==> false)
                    && i₈₀ < N₁₇
                    && a₁₈[i₈₀] == 6 + a[-1 + i₈₀]))
        && (forall i₈₁: int ::
                  0 <= i₈₁
                  && i₈₁ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₈₁] == a[i₈₁])
        && i₁₉ < N₁₇
        && i₁₉ == 0
         ==> i₆ < i₁₉ + 1
          || N₁₇ <= 0
          || a₁₈[0 := 6][0] == a[0]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, a₁₈: [int]int, i₁₉: int, i₆: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₉₆: int ::
              (  0 <= i₉₆
                && i₉₆ < i₁₉
                 ==> i₉₆ == 0
                    && i₉₆ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₉₆ == 0
                       ==> false)
                    && i₉₆ < N₁₇
                    && a₁₈[i₉₆] == 6 + a[-1 + i₉₆]))
        && (forall i₉₇: int ::
                  0 <= i₉₇
                  && i₉₇ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₉₇] == a[i₉₇])
        && i₁₉ < N₁₇
        && 0 <= i₆
        && i₆ < i₁₉ + 1
         ==> i₁₉ == 0
          || N₁₇ <= 0
          ||   i₆ == 0
            && i₆ < N₁₇
            && a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + 6][0] == 6
          ||   (i₆ == 0
               ==> false)
            && i₆ < N₁₇
            && a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + 6][i₆] == 6 + a[-1 + i₆]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, b: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, i₉: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₉
                 ==> i₆ == 0
                    && i₆ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₆ == 0
                       ==> false)
                    && i₆ < N₁₇
                    && a₁₈[i₆] == 6 + a[-1 + i₆]))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₆] == a[i₆])
        && 0 <= i₂₁
        && (forall i₁₇₅: int ::
              (  0 <= i₁₇₅
                && i₁₇₅ < i₂₁
                 ==> i₁₇₅ == 0
                    && i₁₇₅ < N₁₇
                    && b₂₀[0] == 1
                  ||   (i₁₇₅ == 0
                       ==> false)
                    && i₁₇₅ < N₁₇
                    && b₂₀[i₁₇₅] == b[-1 + i₁₇₅] + a₁₈[-1 + i₁₇₅]))
        && (forall i₁₇₆: int ::
                  0 <= i₁₇₆
                  && i₁₇₆ < i₂₁
                ||   b₂₀[0] == b[0]
                  && b₂₀[i₁₇₆] == b[i₁₇₆])
        && i₂₁ < N₁₇
        && i₂₁ == 0
         ==> 0 <= i₉
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || b₂₀[0 := 1][0] == b[0]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, b: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, i₉: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₉
                 ==> i₆ == 0
                    && i₆ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₆ == 0
                       ==> false)
                    && i₆ < N₁₇
                    && a₁₈[i₆] == 6 + a[-1 + i₆]))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₆] == a[i₆])
        && 0 <= i₂₁
        && (forall i₁₉₃: int ::
              (  0 <= i₁₉₃
                && i₁₉₃ < i₂₁
                 ==> i₁₉₃ == 0
                    && i₁₉₃ < N₁₇
                    && b₂₀[0] == 1
                  ||   (i₁₉₃ == 0
                       ==> false)
                    && i₁₉₃ < N₁₇
                    && b₂₀[i₁₉₃] == b[-1 + i₁₉₃] + a₁₈[-1 + i₁₉₃]))
        && (forall i₁₉₄: int ::
                  0 <= i₁₉₄
                  && i₁₉₄ < i₂₁
                ||   b₂₀[0] == b[0]
                  && b₂₀[i₁₉₄] == b[i₁₉₄])
        && i₂₁ < N₁₇
        && i₂₁ == 0
         ==> i₉ < i₂₁ + 1
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || b₂₀[0 := 1][0] == b[0]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, b: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, i₉: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₉
                 ==> i₆ == 0
                    && i₆ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₆ == 0
                       ==> false)
                    && i₆ < N₁₇
                    && a₁₈[i₆] == 6 + a[-1 + i₆]))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₆] == a[i₆])
        && 0 <= i₂₁
        && (forall i₂₁₈: int ::
              (  0 <= i₂₁₈
                && i₂₁₈ < i₂₁
                 ==> i₂₁₈ == 0
                    && i₂₁₈ < N₁₇
                    && b₂₀[0] == 1
                  ||   (i₂₁₈ == 0
                       ==> false)
                    && i₂₁₈ < N₁₇
                    && b₂₀[i₂₁₈] == b[-1 + i₂₁₈] + a₁₈[-1 + i₂₁₈]))
        && (forall i₂₁₉: int ::
                  0 <= i₂₁₉
                  && i₂₁₉ < i₂₁
                ||   b₂₀[0] == b[0]
                  && b₂₀[i₂₁₉] == b[i₂₁₉])
        && i₂₁ < N₁₇
        && 0 <= i₉
        && i₉ < i₂₁ + 1
         ==> i₂₁ == 0
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          ||   i₉ == 0
            && i₉ < N₁₇
            && b₂₀[i₂₁ := b₂₀[i₂₁ - 1] + a₁₈[i₂₁ - 1]][0] == 1
          ||   (i₉ == 0
               ==> false)
            && i₉ < N₁₇
            && b₂₀[i₂₁ := b₂₀[i₂₁ - 1] + a₁₈[i₂₁ - 1]][i₉] == b[-1 + i₉] + a₁₈[-1 + i₉]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, b: [int]int, c: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, c₂₂: [int]int, i₂₃: int, i₁₂: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₉
                 ==> i₆ == 0
                    && i₆ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₆ == 0
                       ==> false)
                    && i₆ < N₁₇
                    && a₁₈[i₆] == 6 + a[-1 + i₆]))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₆] == a[i₆])
        && 0 <= i₂₁
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₁
                 ==> i₉ == 0
                    && i₉ < N₁₇
                    && b₂₀[0] == 1
                  ||   (i₉ == 0
                       ==> false)
                    && i₉ < N₁₇
                    && b₂₀[i₉] == b[-1 + i₉] + a₁₈[-1 + i₉]))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₁
                ||   b₂₀[0] == b[0]
                  && b₂₀[i₉] == b[i₉])
        && 0 <= i₂₃
        && (forall i₃₃₆: int ::
              (  0 <= i₃₃₆
                && i₃₃₆ < i₂₃
                 ==> i₃₃₆ == 0
                    && i₃₃₆ < N₁₇
                    && c₂₂[0] == 0
                  ||   (i₃₃₆ == 0
                       ==> false)
                    && i₃₃₆ < N₁₇
                    && c₂₂[i₃₃₆] == c[-1 + i₃₃₆] + b₂₀[-1 + i₃₃₆]))
        && (forall i₃₃₇: int ::
                  0 <= i₃₃₇
                  && i₃₃₇ < i₂₃
                ||   c₂₂[0] == c[0]
                  && c₂₂[i₃₃₇] == c[i₃₃₇])
        && i₂₃ < N₁₇
        && i₂₃ == 0
         ==> 0 <= i₁₂
          || i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || c₂₂[0 := 0][0] == c[0]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, b: [int]int, c: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, c₂₂: [int]int, i₂₃: int, i₁₂: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₉
                 ==> i₆ == 0
                    && i₆ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₆ == 0
                       ==> false)
                    && i₆ < N₁₇
                    && a₁₈[i₆] == 6 + a[-1 + i₆]))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₆] == a[i₆])
        && 0 <= i₂₁
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₁
                 ==> i₉ == 0
                    && i₉ < N₁₇
                    && b₂₀[0] == 1
                  ||   (i₉ == 0
                       ==> false)
                    && i₉ < N₁₇
                    && b₂₀[i₉] == b[-1 + i₉] + a₁₈[-1 + i₉]))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₁
                ||   b₂₀[0] == b[0]
                  && b₂₀[i₉] == b[i₉])
        && 0 <= i₂₃
        && (forall i₃₆₀: int ::
              (  0 <= i₃₆₀
                && i₃₆₀ < i₂₃
                 ==> i₃₆₀ == 0
                    && i₃₆₀ < N₁₇
                    && c₂₂[0] == 0
                  ||   (i₃₆₀ == 0
                       ==> false)
                    && i₃₆₀ < N₁₇
                    && c₂₂[i₃₆₀] == c[-1 + i₃₆₀] + b₂₀[-1 + i₃₆₀]))
        && (forall i₃₆₁: int ::
                  0 <= i₃₆₁
                  && i₃₆₁ < i₂₃
                ||   c₂₂[0] == c[0]
                  && c₂₂[i₃₆₁] == c[i₃₆₁])
        && i₂₃ < N₁₇
        && i₂₃ == 0
         ==> i₁₂ < i₂₃ + 1
          || i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || c₂₂[0 := 0][0] == c[0]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, b: [int]int, c: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, c₂₂: [int]int, i₂₃: int, i₁₂: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₉
                 ==> i₆ == 0
                    && i₆ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₆ == 0
                       ==> false)
                    && i₆ < N₁₇
                    && a₁₈[i₆] == 6 + a[-1 + i₆]))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₆] == a[i₆])
        && 0 <= i₂₁
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₁
                 ==> i₉ == 0
                    && i₉ < N₁₇
                    && b₂₀[0] == 1
                  ||   (i₉ == 0
                       ==> false)
                    && i₉ < N₁₇
                    && b₂₀[i₉] == b[-1 + i₉] + a₁₈[-1 + i₉]))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₁
                ||   b₂₀[0] == b[0]
                  && b₂₀[i₉] == b[i₉])
        && 0 <= i₂₃
        && (forall i₃₉₄: int ::
              (  0 <= i₃₉₄
                && i₃₉₄ < i₂₃
                 ==> i₃₉₄ == 0
                    && i₃₉₄ < N₁₇
                    && c₂₂[0] == 0
                  ||   (i₃₉₄ == 0
                       ==> false)
                    && i₃₉₄ < N₁₇
                    && c₂₂[i₃₉₄] == c[-1 + i₃₉₄] + b₂₀[-1 + i₃₉₄]))
        && (forall i₃₉₅: int ::
                  0 <= i₃₉₅
                  && i₃₉₅ < i₂₃
                ||   c₂₂[0] == c[0]
                  && c₂₂[i₃₉₅] == c[i₃₉₅])
        && i₂₃ < N₁₇
        && 0 <= i₁₂
        && i₁₂ < i₂₃ + 1
         ==> i₂₃ == 0
          || i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          ||   i₁₂ == 0
            && i₁₂ < N₁₇
            && c₂₂[i₂₃ := c₂₂[i₂₃ - 1] + b₂₀[i₂₃ - 1]][0] == 0
          ||   (i₁₂ == 0
               ==> false)
            && i₁₂ < N₁₇
            && c₂₂[i₂₃ := c₂₂[i₂₃ - 1] + b₂₀[i₂₃ - 1]][i₁₂] == c[-1 + i₁₂] + b₂₀[-1 + i₁₂]));

goal {:named "assert"} (forall N₁₇: int, a: [int]int, b: [int]int, c: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, c₂₂: [int]int, i₂₃: int, i₂₄: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₉
                 ==> i₆ == 0
                    && i₆ < N₁₇
                    && a₁₈[0] == 6
                  ||   (i₆ == 0
                       ==> false)
                    && i₆ < N₁₇
                    && a₁₈[i₆] == 6 + a[-1 + i₆]))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₉
                ||   a₁₈[0] == a[0]
                  && a₁₈[i₆] == a[i₆])
        && 0 <= i₂₁
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₁
                 ==> i₉ == 0
                    && i₉ < N₁₇
                    && b₂₀[0] == 1
                  ||   (i₉ == 0
                       ==> false)
                    && i₉ < N₁₇
                    && b₂₀[i₉] == b[-1 + i₉] + a₁₈[-1 + i₉]))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₁
                ||   b₂₀[0] == b[0]
                  && b₂₀[i₉] == b[i₉])
        && 0 <= i₂₃
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₂₃
                 ==> i₁₂ == 0
                    && i₁₂ < N₁₇
                    && c₂₂[0] == 0
                  ||   (i₁₂ == 0
                       ==> false)
                    && i₁₂ < N₁₇
                    && c₂₂[i₁₂] == c[-1 + i₁₂] + b₂₀[-1 + i₁₂]))
        && (forall i₁₂: int ::
                  0 <= i₁₂
                  && i₁₂ < i₂₃
                ||   c₂₂[0] == c[0]
                  && c₂₂[i₁₂] == c[i₁₂])
        && 0 <= i₂₄
        && (forall i₁₅: int ::
              (  0 <= i₁₅
                && i₁₅ < i₂₄
                 ==> i₁₅ < N₁₇))
        && i₂₄ < N₁₇
         ==> i₂₃ < N₁₇
          || i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || c₂₂[i₂₄] == i₂₄ * i₂₄ * i₂₄));

