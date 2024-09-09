goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₂₀₃: int, m₂₀₄: int, i₂₀₅: int ::
              (  0 <= i₂₀₅
                && 1 <= blength₂₀₃
                && blength₂₀₃ < blength₉
                && 0 <= i₂₀₅
                && i₂₀₅ < i₁₁
                 ==> a[i₂₀₅] < a[m₂₀₄]
                    && i₂₀₅ < alength
                    && 0 <= i₂₀₅
                    && b₈[i₂₀₅] == a[i₂₀₅]
                  ||   (a[i₂₀₅] < a[m₂₀₄]
                       ==> false)
                    && i₂₀₅ < alength
                    && 0 <= i₂₀₅))
        && (forall blength₂₀₆: int, i₂₀₇: int ::
              (0 <= i₂₀₇
                 ==> 1 <= blength₂₀₆
                    && blength₂₀₆ < blength₉
                    && 0 <= i₂₀₇
                    && i₂₀₇ < i₁₁
                  || b₈[i₂₀₇] == b[0 := a[0]][i₂₀₇]))
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
        && 0 <= i₃
        && 1 <= blength₁
        && blength₁ < blength₉ + 1
        && 0 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] < a[m₂]
         ==> b₈[i₁₁ := a[i₁₁]][i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₂₃₅: int, m₂: int, i₂₃₆: int ::
              (  0 <= i₂₃₆
                && 1 <= blength₂₃₅
                && blength₂₃₅ < blength₉
                && 0 <= i₂₃₆
                && i₂₃₆ < i₁₁
                 ==> a[i₂₃₆] < a[m₂]
                    && i₂₃₆ < alength
                    && 0 <= i₂₃₆
                    && b₈[i₂₃₆] == a[i₂₃₆]
                  ||   (a[i₂₃₆] < a[m₂]
                       ==> false)
                    && i₂₃₆ < alength
                    && 0 <= i₂₃₆))
        && (forall blength₂₃₇: int, i₂₃₈: int ::
              (0 <= i₂₃₈
                 ==> 1 <= blength₂₃₇
                    && blength₂₃₇ < blength₉
                    && 0 <= i₂₃₈
                    && i₂₃₈ < i₁₁
                  || b₈[i₂₃₈] == b[0 := a[0]][i₂₃₈]))
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
        && 0 <= i₃
         ==> 1 <= blength₁
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₂₄₈: int, m₂: int, i₂₄₉: int ::
              (  0 <= i₂₄₉
                && 1 <= blength₂₄₈
                && blength₂₄₈ < blength₉
                && 0 <= i₂₄₉
                && i₂₄₉ < i₁₁
                 ==> a[i₂₄₉] < a[m₂]
                    && i₂₄₉ < alength
                    && 0 <= i₂₄₉
                    && b₈[i₂₄₉] == a[i₂₄₉]
                  ||   (a[i₂₄₉] < a[m₂]
                       ==> false)
                    && i₂₄₉ < alength
                    && 0 <= i₂₄₉))
        && (forall blength₂₅₀: int, i₂₅₁: int ::
              (0 <= i₂₅₁
                 ==> 1 <= blength₂₅₀
                    && blength₂₅₀ < blength₉
                    && 0 <= i₂₅₁
                    && i₂₅₁ < i₁₁
                  || b₈[i₂₅₁] == b[0 := a[0]][i₂₅₁]))
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
        && 0 <= i₃
         ==> blength₁ < blength₉ + 1
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₃₇₈: int, m₃₇₉: int, i₃₈₀: int ::
              (  0 <= i₃₈₀
                && 1 <= blength₃₇₈
                && blength₃₇₈ < blength₉
                && 0 <= i₃₈₀
                && i₃₈₀ < i₁₁
                 ==> a[i₃₈₀] < a[m₃₇₉]
                    && i₃₈₀ < alength
                    && 0 <= i₃₈₀
                    && b₈[i₃₈₀] == a[i₃₈₀]
                  ||   (a[i₃₈₀] < a[m₃₇₉]
                       ==> false)
                    && i₃₈₀ < alength
                    && 0 <= i₃₈₀))
        && (forall blength₃₈₁: int, i₃₈₂: int ::
              (0 <= i₃₈₂
                 ==> 1 <= blength₃₈₁
                    && blength₃₈₁ < blength₉
                    && 0 <= i₃₈₂
                    && i₃₈₂ < i₁₁
                  || b₈[i₃₈₂] == b[0 := a[0]][i₃₈₂]))
        && i₁₁ < alength
        && 0 <= i₃
        && 1 <= blength₁
        && blength₁ < blength₉
        && 0 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] < a[m₂]
         ==> a[i₁₁] < a[m₁₀]
          || b₈[i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, j: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  0 <= i₃
                && 1 <= blength₁
                && blength₁ < blength₉
                && 0 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] < a[m₂]
                    && i₃ < alength
                    && 0 <= i₃
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] < a[m₂]
                       ==> false)
                    && i₃ < alength
                    && 0 <= i₃))
        && (forall blength₁: int, i₃: int ::
              (0 <= i₃
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
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  0 <= i₃
                && 1 <= blength₁
                && blength₁ < blength₉
                && 0 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] < a[m₂]
                    && i₃ < alength
                    && 0 <= i₃
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] < a[m₂]
                       ==> false)
                    && i₃ < alength
                    && 0 <= i₃))
        && (forall blength₁: int, i₃: int ::
              (0 <= i₃
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

