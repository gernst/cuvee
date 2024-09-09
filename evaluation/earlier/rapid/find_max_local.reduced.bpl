goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₁₇₉: int, m₁₈₀: int, i₁₈₁: int ::
              (  0 <= i₁₈₁
                && 1 <= blength₁₇₉
                && blength₁₇₉ < blength₉
                && 1 <= i₁₈₁
                && i₁₈₁ < i₁₁
                 ==> a[i₁₈₁] > a[m₁₈₀]
                    && i₁₈₁ < alength
                    && 0 <= i₁₈₁
                    && b₈[i₁₈₁] == a[i₁₈₁]
                  ||   (a[i₁₈₁] > a[m₁₈₀]
                       ==> false)
                    && i₁₈₁ < alength
                    && 0 <= i₁₈₁))
        && i₁₁ < alength
        && a[i₁₁] > a[m₁₀]
        && 0 <= i₃
        && 1 <= blength₁
        && blength₁ < blength₉ + 1
        && 1 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] > a[m₂]
         ==> b₈[i₁₁ := a[i₁₁]][i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₃₀₂: int, m₃₀₃: int, i₃₀₄: int ::
              (  0 <= i₃₀₄
                && 1 <= blength₃₀₂
                && blength₃₀₂ < blength₉
                && 1 <= i₃₀₄
                && i₃₀₄ < i₁₁
                 ==> a[i₃₀₄] > a[m₃₀₃]
                    && i₃₀₄ < alength
                    && 0 <= i₃₀₄
                    && b₈[i₃₀₄] == a[i₃₀₄]
                  ||   (a[i₃₀₄] > a[m₃₀₃]
                       ==> false)
                    && i₃₀₄ < alength
                    && 0 <= i₃₀₄))
        && i₁₁ < alength
        && 0 <= i₃
        && 1 <= blength₁
        && blength₁ < blength₉
        && 1 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] > a[m₂]
         ==> a[i₁₁] > a[m₁₀]
          || b₈[i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, i₁₁: int, k: int ::
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

goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, i₁₁: int, j: int ::
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
         ==> i₁₁ < alength
          || (exists k: int ::
                (  1 <= alength
                  && 0 <= j
                  && j < blength₉
                   ==> 0 <= k
                    && k < alength
                    && b₈[j] == a[k]))));

goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, i₁₁: int, j: int, k: int ::
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
        && 1 <= alength
        && 0 <= j
        && 0 <= k
        && j <= k
        && k < blength₉
         ==> i₁₁ < alength
          || b₈[j] <= b₈[k]));

