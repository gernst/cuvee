goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₂₁₁: int, m₂₁₂: int, i₂₁₃: int ::
              (  1 <= blength₂₁₁
                && blength₂₁₁ < blength₉
                && 0 <= i₂₁₃
                && i₂₁₃ < i₁₁
                 ==> a[i₂₁₃] < a[m₂₁₂]
                    && i₂₁₃ < alength
                    && 0 <= i₂₁₃
                    && b₈[i₂₁₃] == a[i₂₁₃]
                  ||   (a[i₂₁₃] < a[m₂₁₂]
                       ==> false)
                    && i₂₁₃ < alength
                    && 0 <= i₂₁₃))
        && (forall blength₂₁₄: int, i₂₁₅: int ::
                  1 <= blength₂₁₄
                  && blength₂₁₄ < blength₉
                  && 0 <= i₂₁₅
                  && i₂₁₅ < i₁₁
                || b₈[i₂₁₅] == b[0 := a[0]][i₂₁₅])
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
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
        && i₁₁ <= alength
        && (forall blength₂₄₃: int, m₂: int, i₂₄₄: int ::
              (  1 <= blength₂₄₃
                && blength₂₄₃ < blength₉
                && 0 <= i₂₄₄
                && i₂₄₄ < i₁₁
                 ==> a[i₂₄₄] < a[m₂]
                    && i₂₄₄ < alength
                    && 0 <= i₂₄₄
                    && b₈[i₂₄₄] == a[i₂₄₄]
                  ||   (a[i₂₄₄] < a[m₂]
                       ==> false)
                    && i₂₄₄ < alength
                    && 0 <= i₂₄₄))
        && (forall blength₂₄₅: int, i₂₄₆: int ::
                  1 <= blength₂₄₅
                  && blength₂₄₅ < blength₉
                  && 0 <= i₂₄₆
                  && i₂₄₆ < i₁₁
                || b₈[i₂₄₆] == b[0 := a[0]][i₂₄₆])
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
         ==> 1 <= blength₁
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₂₅₆: int, m₂: int, i₂₅₇: int ::
              (  1 <= blength₂₅₆
                && blength₂₅₆ < blength₉
                && 0 <= i₂₅₇
                && i₂₅₇ < i₁₁
                 ==> a[i₂₅₇] < a[m₂]
                    && i₂₅₇ < alength
                    && 0 <= i₂₅₇
                    && b₈[i₂₅₇] == a[i₂₅₇]
                  ||   (a[i₂₅₇] < a[m₂]
                       ==> false)
                    && i₂₅₇ < alength
                    && 0 <= i₂₅₇))
        && (forall blength₂₅₈: int, i₂₅₉: int ::
                  1 <= blength₂₅₈
                  && blength₂₅₈ < blength₉
                  && 0 <= i₂₅₉
                  && i₂₅₉ < i₁₁
                || b₈[i₂₅₉] == b[0 := a[0]][i₂₅₉])
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
         ==> blength₁ < blength₉ + 1
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₃₉₃: int, m₃₉₄: int, i₃₉₅: int ::
              (  1 <= blength₃₉₃
                && blength₃₉₃ < blength₉
                && 0 <= i₃₉₅
                && i₃₉₅ < i₁₁
                 ==> a[i₃₉₅] < a[m₃₉₄]
                    && i₃₉₅ < alength
                    && 0 <= i₃₉₅
                    && b₈[i₃₉₅] == a[i₃₉₅]
                  ||   (a[i₃₉₅] < a[m₃₉₄]
                       ==> false)
                    && i₃₉₅ < alength
                    && 0 <= i₃₉₅))
        && (forall blength₃₉₆: int, i₃₉₇: int ::
                  1 <= blength₃₉₆
                  && blength₃₉₆ < blength₉
                  && 0 <= i₃₉₇
                  && i₃₉₇ < i₁₁
                || b₈[i₃₉₇] == b[0 := a[0]][i₃₉₇])
        && i₁₁ < alength
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
        && i₁₁ <= alength
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  1 <= blength₁
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
                  1 <= blength₁
                  && blength₁ < blength₉
                  && 0 <= i₃
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
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && i₁₁ <= alength
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  1 <= blength₁
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
                  1 <= blength₁
                  && blength₁ < blength₉
                  && 0 <= i₃
                  && i₃ < i₁₁
                || b₈[i₃] == b[0 := a[0]][i₃])
        && 1 <= alength
        && 0 <= j
        && 0 <= k
        && j <= k
        && k < blength₉
         ==> i₁₁ < alength
          || b₈[k] <= b₈[j]));

