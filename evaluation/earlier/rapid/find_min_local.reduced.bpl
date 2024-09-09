goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₁₇₃: int, m₁₇₄: int, i₁₇₅: int ::
              (  0 <= i₁₇₅
                && 1 <= blength₁₇₃
                && blength₁₇₃ < blength₉
                && 0 <= i₁₇₅
                && i₁₇₅ < i₁₁
                 ==> a[i₁₇₅] < a[m₁₇₄]
                    && i₁₇₅ < alength
                    && 0 <= i₁₇₅
                    && b₈[i₁₇₅] == a[i₁₇₅]
                  ||   (a[i₁₇₅] < a[m₁₇₄]
                       ==> false)
                    && i₁₇₅ < alength
                    && 0 <= i₁₇₅))
        && i₁₁ < alength
        && a[i₁₁] < a[m₁₀]
        && 0 <= i₃
        && 1 <= blength₁
        && blength₁ < blength₉ + 1
        && 0 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] < a[m₂]
         ==> b₈[i₁₁ := a[i₁₁]][i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, m₁₀: int, i₁₁: int, blength₁: int, m₂: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₁
        && 1 <= blength₉
        && 0 <= i₁₁
        && (forall blength₂₉₀: int, m₂₉₁: int, i₂₉₂: int ::
              (  0 <= i₂₉₂
                && 1 <= blength₂₉₀
                && blength₂₉₀ < blength₉
                && 0 <= i₂₉₂
                && i₂₉₂ < i₁₁
                 ==> a[i₂₉₂] < a[m₂₉₁]
                    && i₂₉₂ < alength
                    && 0 <= i₂₉₂
                    && b₈[i₂₉₂] == a[i₂₉₂]
                  ||   (a[i₂₉₂] < a[m₂₉₁]
                       ==> false)
                    && i₂₉₂ < alength
                    && 0 <= i₂₉₂))
        && i₁₁ < alength
        && 0 <= i₃
        && 1 <= blength₁
        && blength₁ < blength₉
        && 0 <= i₃
        && i₃ < i₁₁ + 1
        && a[i₃] < a[m₂]
         ==> a[i₁₁] < a[m₁₀]
          || b₈[i₃] == a[i₃]));

goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, i₁₁: int, k: int ::
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
        && 1 <= alength
        && 0 <= k
        && k < alength
        && (forall l: int ::
              (  0 <= l
                && l < k
                 ==> a[k] == a[l]))
         ==> i₁₁ < alength
          || (exists j: int ::
                  0 <= j
                  && j < blength₉
                  && a[k] == b₈[j])));

goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, i₁₁: int, j: int ::
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
         ==> i₁₁ < alength
          || (exists k: int ::
                (  1 <= alength
                  && 0 <= j
                  && j < blength₉
                   ==> 0 <= k
                    && k < alength
                    && b₈[j] == a[k]))));

goal (forall a: [int]int, alength: int, b₈: [int]int, blength₉: int, i₁₁: int, j: int, k: int ::
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
        && 1 <= alength
        && 0 <= j
        && 0 <= k
        && j <= k
        && k < blength₉
         ==> i₁₁ < alength
          || b₈[k] <= b₈[j]));

