goal (forall alength: int ::
      (0 <= alength
         ==> 1 + 1 == 0 + 0));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  0 <= alength
        && 1 + blength₉ == i₁₁ + 0
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁₄₂: int, m₁₄₃: int, i₁₄₄: int ::
              (  blength₁₄₂ + blength₁₄₂ == i₁₄₄ + i₁₄₄
                && 1 <= blength₁₄₂
                && blength₁₄₂ < blength₉
                && 0 <= i₁₄₄
                && i₁₄₄ < i₁₁
                 ==> a[i₁₄₄] < a[m₁₄₃]
                    && i₁₄₄ < alength
                    && b₈[i₁₄₄] == a[i₁₄₄]
                  ||   (a[i₁₄₄] < a[m₁₄₃]
                       ==> false)
                    && i₁₄₄ < alength))
        && (forall blength₁₄₅: int, i₁₄₆: int ::
              (blength₁₄₅ + blength₁₄₅ == i₁₄₆ + i₁₄₆
                 ==> 1 <= blength₁₄₅
                    && blength₁₄₅ < blength₉
                    && 0 <= i₁₄₆
                    && i₁₄₆ < i₁₁
                  || b₈[i₁₄₆] == b[0 := a[0]][i₁₄₆]))
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
        && blength₁ + blength₁ == i₃ + i₃
        && 1 <= blength₁
        && blength₁ < blength₉ + 1
        && 0 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] < a[m₂]
         ==> b₈[i₁₁ := a[i₁₁]][i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, i₃: int ::
      (  0 <= alength
        && 1 + blength₉ == i₁₁ + 0
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁₇₄: int, m₂: int, i₁₇₅: int ::
              (  blength₁₇₄ + blength₁₇₄ == i₁₇₅ + i₁₇₅
                && 1 <= blength₁₇₄
                && blength₁₇₄ < blength₉
                && 0 <= i₁₇₅
                && i₁₇₅ < i₁₁
                 ==> a[i₁₇₅] < a[m₂]
                    && i₁₇₅ < alength
                    && b₈[i₁₇₅] == a[i₁₇₅]
                  ||   (a[i₁₇₅] < a[m₂]
                       ==> false)
                    && i₁₇₅ < alength))
        && (forall blength₁₇₆: int, i₁₇₇: int ::
              (blength₁₇₆ + blength₁₇₆ == i₁₇₇ + i₁₇₇
                 ==> 1 <= blength₁₇₆
                    && blength₁₇₆ < blength₉
                    && 0 <= i₁₇₇
                    && i₁₇₇ < i₁₁
                  || b₈[i₁₇₇] == b[0 := a[0]][i₁₇₇]))
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
        && blength₁ + blength₁ == i₃ + i₃
         ==> blength₁ < blength₉ + 1
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int ::
      (  0 <= alength
        && 1 + blength₉ == i₁₁ + 0
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  blength₁ + blength₁ == i₃ + i₃
                && 1 <= blength₁
                && blength₁ < blength₉
                && 0 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] < a[m₂]
                    && i₃ < alength
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] < a[m₂]
                       ==> false)
                    && i₃ < alength))
        && (forall blength₁: int, i₃: int ::
              (blength₁ + blength₁ == i₃ + i₃
                 ==> 1 <= blength₁
                    && blength₁ < blength₉
                    && 0 <= i₃
                    && i₃ < i₁₁
                  || b₈[i₃] == b[0 := a[0]][i₃]))
        && i₁₁ < alength
         ==> a[i₁₁] < a[m₁₀]
          || 1 + blength₉ == i₁₁ + 1 + 0));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, j: int ::
      (  0 <= alength
        && 1 + blength₉ == i₁₁ + 0
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  blength₁ + blength₁ == i₃ + i₃
                && 1 <= blength₁
                && blength₁ < blength₉
                && 0 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] < a[m₂]
                    && i₃ < alength
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] < a[m₂]
                       ==> false)
                    && i₃ < alength))
        && (forall blength₁: int, i₃: int ::
              (blength₁ + blength₁ == i₃ + i₃
                 ==> 1 <= blength₁
                    && blength₁ < blength₉
                    && 0 <= i₃
                    && i₃ < i₁₁
                  || b₈[i₃] == b[0 := a[0]][i₃]))
         ==> i₁₁ < alength
          || (exists k: int ::
                (  1 <= alength
                  && 0 <= j
                  && j < blength₉
                   ==> 0 <= k
                    && k < alength
                    && b₈[j] == a[k]))));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, j: int, k: int ::
      (  0 <= alength
        && 1 + blength₉ == i₁₁ + 0
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  blength₁ + blength₁ == i₃ + i₃
                && 1 <= blength₁
                && blength₁ < blength₉
                && 0 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] < a[m₂]
                    && i₃ < alength
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] < a[m₂]
                       ==> false)
                    && i₃ < alength))
        && (forall blength₁: int, i₃: int ::
              (blength₁ + blength₁ == i₃ + i₃
                 ==> 1 <= blength₁
                    && blength₁ < blength₉
                    && 0 <= i₃
                    && i₃ < i₁₁
                  || b₈[i₃] == b[0 := a[0]][i₃]))
        && 1 <= alength
        && 0 <= j
        && 0 <= k
        && j <= k
        && k < blength₉
         ==> i₁₁ < alength
          || b₈[k] <= b₈[j]));

