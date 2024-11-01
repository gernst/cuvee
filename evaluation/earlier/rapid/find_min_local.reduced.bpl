goal {:named "invariant entry"} (forall alength: int ::
      (0 <= alength
         ==> 1 + 1 == 0 + 0));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  0 <= alength
        && 1 + blength₉ == i₁₁ + 0
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₈₀: int, m₈₁: int, i₈₂: int ::
              (  blength₈₀ + blength₈₀ == i₈₂ + i₈₂
                && 1 <= blength₈₀
                && blength₈₀ < blength₉
                && 0 <= i₈₂
                && i₈₂ < i₁₁
                 ==> a[i₈₂] < a[m₈₁]
                    && i₈₂ < alength
                    && b₈[i₈₂] == a[i₈₂]
                  ||   (a[i₈₂] < a[m₈₁]
                       ==> false)
                    && i₈₂ < alength))
        && (forall blength₈₃: int, i₈₄: int ::
              (blength₈₃ + blength₈₃ == i₈₄ + i₈₄
                 ==> 1 <= blength₈₃
                    && blength₈₃ < blength₉
                    && 0 <= i₈₄
                    && i₈₄ < i₁₁
                  || b₈[i₈₄] == b[0 := a[0]][i₈₄]))
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
        && blength₁ + blength₁ == i₃ + i₃
        && 1 <= blength₁
        && blength₁ < blength₉ + 1
        && 0 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] < a[m₂]
         ==> a[i₃] < a[m₂]
          && i₃ < alength
          && b₈[i₁₁ := a[i₁₁]][i₃] == a[i₃]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, i₃: int ::
      (  0 <= alength
        && 1 + blength₉ == i₁₁ + 0
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁₀₃: int, m₂: int, i₁₀₄: int ::
              (  blength₁₀₃ + blength₁₀₃ == i₁₀₄ + i₁₀₄
                && 1 <= blength₁₀₃
                && blength₁₀₃ < blength₉
                && 0 <= i₁₀₄
                && i₁₀₄ < i₁₁
                 ==> a[i₁₀₄] < a[m₂]
                    && i₁₀₄ < alength
                    && b₈[i₁₀₄] == a[i₁₀₄]
                  ||   (a[i₁₀₄] < a[m₂]
                       ==> false)
                    && i₁₀₄ < alength))
        && (forall blength₁₀₅: int, i₁₀₆: int ::
              (blength₁₀₅ + blength₁₀₅ == i₁₀₆ + i₁₀₆
                 ==> 1 <= blength₁₀₅
                    && blength₁₀₅ < blength₉
                    && 0 <= i₁₀₆
                    && i₁₀₆ < i₁₁
                  || b₈[i₁₀₆] == b[0 := a[0]][i₁₀₆]))
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
        && blength₁ + blength₁ == i₃ + i₃
         ==> blength₁ < blength₉ + 1
          || b₈[i₁₁ := a[i₁₁]][i₃] == b[0 := a[0]][i₃]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int ::
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

goal {:named "ensures"} (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, j: int ::
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

goal {:named "ensures"} (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, j: int, k: int ::
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

