goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₂₁₈: int, m₂₁₉: int, i₂₂₀: int ::
              (  1 <= blength₂₁₈
                && blength₂₁₈ < blength₉
                && 1 <= i₂₂₀
                && i₂₂₀ < i₁₁
                 ==> a[i₂₂₀] > a[m₂₁₉]
                    && i₂₂₀ < alength
                    && 0 <= i₂₂₀
                    && b₈[i₂₂₀] == a[i₂₂₀]
                  ||   (a[i₂₂₀] > a[m₂₁₉]
                       ==> false)
                    && i₂₂₀ < alength
                    && 0 <= i₂₂₀))
        && (forall blength₂₂₁: int, i₂₂₂: int ::
                  1 <= blength₂₂₁
                  && blength₂₂₁ < blength₉
                  && 1 <= i₂₂₂
                  && i₂₂₂ < i₁₁
                || b₈[i₂₂₂] == b[0 := a[0]][i₂₂₂])
        && i₁₁ < alength
        && a[i₁₁] > a[m₁₀]
        && 1 <= blength₁
        && blength₁ < blength₉ + 1
        && 1 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] > a[m₂]
         ==> b₈[i₁₁ := a[i₁₁]][i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₂₅₀: int, m₂: int, i₂₅₁: int ::
              (  1 <= blength₂₅₀
                && blength₂₅₀ < blength₉
                && 1 <= i₂₅₁
                && i₂₅₁ < i₁₁
                 ==> a[i₂₅₁] > a[m₂]
                    && i₂₅₁ < alength
                    && 0 <= i₂₅₁
                    && b₈[i₂₅₁] == a[i₂₅₁]
                  ||   (a[i₂₅₁] > a[m₂]
                       ==> false)
                    && i₂₅₁ < alength
                    && 0 <= i₂₅₁))
        && (forall blength₂₅₂: int, i₂₅₃: int ::
                  1 <= blength₂₅₂
                  && blength₂₅₂ < blength₉
                  && 1 <= i₂₅₃
                  && i₂₅₃ < i₁₁
                || b₈[i₂₅₃] == b[0 := a[0]][i₂₅₃])
        && i₁₁ < alength
        && a[i₁₁] > a[m₁₀]
         ==> 1 <= blength₁
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₂₆₃: int, m₂: int, i₂₆₄: int ::
              (  1 <= blength₂₆₃
                && blength₂₆₃ < blength₉
                && 1 <= i₂₆₄
                && i₂₆₄ < i₁₁
                 ==> a[i₂₆₄] > a[m₂]
                    && i₂₆₄ < alength
                    && 0 <= i₂₆₄
                    && b₈[i₂₆₄] == a[i₂₆₄]
                  ||   (a[i₂₆₄] > a[m₂]
                       ==> false)
                    && i₂₆₄ < alength
                    && 0 <= i₂₆₄))
        && (forall blength₂₆₅: int, i₂₆₆: int ::
                  1 <= blength₂₆₅
                  && blength₂₆₅ < blength₉
                  && 1 <= i₂₆₆
                  && i₂₆₆ < i₁₁
                || b₈[i₂₆₆] == b[0 := a[0]][i₂₆₆])
        && i₁₁ < alength
        && a[i₁₁] > a[m₁₀]
         ==> blength₁ < blength₉ + 1
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₄₀₇: int, m₄₀₈: int, i₄₀₉: int ::
              (  1 <= blength₄₀₇
                && blength₄₀₇ < blength₉
                && 1 <= i₄₀₉
                && i₄₀₉ < i₁₁
                 ==> a[i₄₀₉] > a[m₄₀₈]
                    && i₄₀₉ < alength
                    && 0 <= i₄₀₉
                    && b₈[i₄₀₉] == a[i₄₀₉]
                  ||   (a[i₄₀₉] > a[m₄₀₈]
                       ==> false)
                    && i₄₀₉ < alength
                    && 0 <= i₄₀₉))
        && (forall blength₄₁₀: int, i₄₁₁: int ::
                  1 <= blength₄₁₀
                  && blength₄₁₀ < blength₉
                  && 1 <= i₄₁₁
                  && i₄₁₁ < i₁₁
                || b₈[i₄₁₁] == b[0 := a[0]][i₄₁₁])
        && i₁₁ < alength
        && 1 <= blength₁
        && blength₁ < blength₉
        && 1 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] > a[m₂]
         ==> a[i₁₁] > a[m₁₀]
          || b₈[i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, k: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  1 <= blength₁
                && blength₁ < blength₉
                && 1 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] > a[m₂]
                    && i₃ < alength
                    && 0 <= i₃
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] > a[m₂]
                       ==> false)
                    && i₃ < alength
                    && 0 <= i₃))
        && (forall blength₁: int, i₃: int ::
                  1 <= blength₁
                  && blength₁ < blength₉
                  && 1 <= i₃
                  && i₃ < i₁₁
                || b₈[i₃] == b[0 := a[0]][i₃])
        && 1 <= alength
        && 0 <= k
        && k < alength
        && (forall l: int ::
              (  0 <= l
                && l < k
                 ==> a[l] < a[k]))
         ==> i₁₁ < alength
          || (exists j: int ::
                  0 <= j
                  && j < blength₉
                  && a[k] == b₈[j])));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, j: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  1 <= blength₁
                && blength₁ < blength₉
                && 1 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] > a[m₂]
                    && i₃ < alength
                    && 0 <= i₃
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] > a[m₂]
                       ==> false)
                    && i₃ < alength
                    && 0 <= i₃))
        && (forall blength₁: int, i₃: int ::
                  1 <= blength₁
                  && blength₁ < blength₉
                  && 1 <= i₃
                  && i₃ < i₁₁
                || b₈[i₃] == b[0 := a[0]][i₃])
         ==> i₁₁ < alength
          || (exists k: int ::
                (  1 <= alength
                  && 0 <= j
                  && j < blength₉
                   ==> 0 <= k
                    && k < alength
                    && b₈[j] == a[k]))));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, j: int, k: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  1 <= blength₁
                && blength₁ < blength₉
                && 1 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] > a[m₂]
                    && i₃ < alength
                    && 0 <= i₃
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] > a[m₂]
                       ==> false)
                    && i₃ < alength
                    && 0 <= i₃))
        && (forall blength₁: int, i₃: int ::
                  1 <= blength₁
                  && blength₁ < blength₉
                  && 1 <= i₃
                  && i₃ < i₁₁
                || b₈[i₃] == b[0 := a[0]][i₃])
        && 1 <= alength
        && 0 <= j
        && 0 <= k
        && j <= k
        && k < blength₉
         ==> i₁₁ < alength
          || b₈[j] <= b₈[k]));

