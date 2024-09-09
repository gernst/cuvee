goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int ::
      (  1 <= alength
        && 1 + blength₉ == i₁₁ + 1
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  blength₁ + blength₁ == i₃ + i₃
                && 1 <= blength₁
                && blength₁ < blength₉
                && 1 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] > a[m₂]
                    && i₃ < alength
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] > a[m₂]
                       ==> false)
                    && i₃ < alength))
        && (forall blength₁: int, i₃: int ::
              (blength₁ + blength₁ == i₃ + i₃
                 ==> 1 <= blength₁
                    && blength₁ < blength₉
                    && 1 <= i₃
                    && i₃ < i₁₁
                  || b₈[i₃] == b[0 := a[0]][i₃]))
        && i₁₁ < alength
         ==> a[i₁₁] > a[m₁₀]
          || 1 + blength₉ == i₁₁ + 1 + 1));

goal (forall a: [int]int, alength: int, b: [int]int, b₈: [int]int, blength₉: int, i₁₁: int, j: int ::
      (  1 <= alength
        && 1 + blength₉ == i₁₁ + 1
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  blength₁ + blength₁ == i₃ + i₃
                && 1 <= blength₁
                && blength₁ < blength₉
                && 1 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] > a[m₂]
                    && i₃ < alength
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] > a[m₂]
                       ==> false)
                    && i₃ < alength))
        && (forall blength₁: int, i₃: int ::
              (blength₁ + blength₁ == i₃ + i₃
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
        && 1 + blength₉ == i₁₁ + 1
        && 1 <= blength₉
        && 1 <= i₁₁
        && (forall blength₁: int, m₂: int, i₃: int ::
              (  blength₁ + blength₁ == i₃ + i₃
                && 1 <= blength₁
                && blength₁ < blength₉
                && 1 <= i₃
                && i₃ < i₁₁
                 ==> a[i₃] > a[m₂]
                    && i₃ < alength
                    && b₈[i₃] == a[i₃]
                  ||   (a[i₃] > a[m₂]
                       ==> false)
                    && i₃ < alength))
        && (forall blength₁: int, i₃: int ::
              (blength₁ + blength₁ == i₃ + i₃
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

