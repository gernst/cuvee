goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₂₁₀: int, m₂₁₁: int, i₂₁₂: int ::
              (  0 <= i₂₁₂
                && 1 <= blength₂₁₀
                && blength₂₁₀ < blength₉
                && 1 <= i₂₁₂
                && i₂₁₂ < i₁₁
                 ==> a[i₂₁₂] > a[m₂₁₁]
                    && i₂₁₂ < alength
                    && 0 <= i₂₁₂
                    && b₈[i₂₁₂] == a[i₂₁₂]
                  ||   (a[i₂₁₂] > a[m₂₁₁]
                       ==> false)
                    && i₂₁₂ < alength
                    && 0 <= i₂₁₂))
        && (forall blength₂₁₃: int, i₂₁₄: int ::
              (0 <= i₂₁₄
                 ==> 1 <= blength₂₁₃
                    && blength₂₁₃ < blength₉
                    && 1 <= i₂₁₄
                    && i₂₁₄ < i₁₁
                  || b₈[i₂₁₄] == b[0 := a[0]][i₂₁₄]))
        && i₁₁ < alength
        && a[i₁₁] > a[m₁₀]
        && 0 <= i₃
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
        && (forall blength₂₄₂: int, m₂: int, i₂₄₃: int ::
              (  0 <= i₂₄₃
                && 1 <= blength₂₄₂
                && blength₂₄₂ < blength₉
                && 1 <= i₂₄₃
                && i₂₄₃ < i₁₁
                 ==> a[i₂₄₃] > a[m₂]
                    && i₂₄₃ < alength
                    && 0 <= i₂₄₃
                    && b₈[i₂₄₃] == a[i₂₄₃]
                  ||   (a[i₂₄₃] > a[m₂]
                       ==> false)
                    && i₂₄₃ < alength
                    && 0 <= i₂₄₃))
        && (forall blength₂₄₄: int, i₂₄₅: int ::
              (0 <= i₂₄₅
                 ==> 1 <= blength₂₄₄
                    && blength₂₄₄ < blength₉
                    && 1 <= i₂₄₅
                    && i₂₄₅ < i₁₁
                  || b₈[i₂₄₅] == b[0 := a[0]][i₂₄₅]))
        && i₁₁ < alength
        && a[i₁₁] > a[m₁₀]
        && 0 <= i₃
         ==> 1 <= blength₁
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₂₅₅: int, m₂: int, i₂₅₆: int ::
              (  0 <= i₂₅₆
                && 1 <= blength₂₅₅
                && blength₂₅₅ < blength₉
                && 1 <= i₂₅₆
                && i₂₅₆ < i₁₁
                 ==> a[i₂₅₆] > a[m₂]
                    && i₂₅₆ < alength
                    && 0 <= i₂₅₆
                    && b₈[i₂₅₆] == a[i₂₅₆]
                  ||   (a[i₂₅₆] > a[m₂]
                       ==> false)
                    && i₂₅₆ < alength
                    && 0 <= i₂₅₆))
        && (forall blength₂₅₇: int, i₂₅₈: int ::
              (0 <= i₂₅₈
                 ==> 1 <= blength₂₅₇
                    && blength₂₅₇ < blength₉
                    && 1 <= i₂₅₈
                    && i₂₅₈ < i₁₁
                  || b₈[i₂₅₈] == b[0 := a[0]][i₂₅₈]))
        && i₁₁ < alength
        && a[i₁₁] > a[m₁₀]
        && 0 <= i₃
         ==> blength₁ < blength₉ + 1
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₃₉₂: int, m₃₉₃: int, i₃₉₄: int ::
              (  0 <= i₃₉₄
                && 1 <= blength₃₉₂
                && blength₃₉₂ < blength₉
                && 1 <= i₃₉₄
                && i₃₉₄ < i₁₁
                 ==> a[i₃₉₄] > a[m₃₉₃]
                    && i₃₉₄ < alength
                    && 0 <= i₃₉₄
                    && b₈[i₃₉₄] == a[i₃₉₄]
                  ||   (a[i₃₉₄] > a[m₃₉₃]
                       ==> false)
                    && i₃₉₄ < alength
                    && 0 <= i₃₉₄))
        && (forall blength₃₉₅: int, i₃₉₆: int ::
              (0 <= i₃₉₆
                 ==> 1 <= blength₃₉₅
                    && blength₃₉₅ < blength₉
                    && 1 <= i₃₉₆
                    && i₃₉₆ < i₁₁
                  || b₈[i₃₉₆] == b[0 := a[0]][i₃₉₆]))
        && i₁₁ < alength
        && 0 <= i₃
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
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  0 <= i₃
                && 1 <= blength₁
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
              (0 <= i₃
                 ==> 1 <= blength₁
                    && blength₁ < blength₉
                    && 1 <= i₃
                    && i₃ < i₁₁
                  || b₈[i₃] == b[0 := a[0]][i₃]))
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
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  0 <= i₃
                && 1 <= blength₁
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
              (0 <= i₃
                 ==> 1 <= blength₁
                    && blength₁ < blength₉
                    && 1 <= i₃
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
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  0 <= i₃
                && 1 <= blength₁
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
              (0 <= i₃
                 ==> 1 <= blength₁
                    && blength₁ < blength₉
                    && 1 <= i₃
                    && i₃ < i₁₁
                  || b₈[i₃] == b[0 := a[0]][i₃]))
        && 1 <= alength
        && 0 <= j
        && 0 <= k
        && j <= k
        && k < blength₉
         ==> i₁₁ < alength
          || b₈[j] <= b₈[k]));

