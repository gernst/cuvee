goal (forall a: [int]int, alength: int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₁₁₁: int, i₁₁₀: int ::
              (  0 <= i₁₁₀
                && 0 <= i₁₁₀
                && i₁₁₀ < i₈
                 ==> a[i₁₁₀] < a[m₁₁₁]
                    && i₁₁₀ < alength
                    && 0 <= i₁₁₀
                    && b₆[i₁₁₀] == a[i₁₁₀]
                  ||   (a[i₁₁₀] < a[m₁₁₁]
                       ==> false)
                    && i₁₁₀ < alength
                    && 0 <= i₁₁₀
                    && b₆[i₁₁₀] == a[m₁₁₁]))
        && i₈ < alength
        && a[i₈] < a[m₇]
        && 0 <= i₂
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₂] < a[m₁]
          || b₆[i₈ := a[i₈]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₂₂₄: int, i₂₂₃: int ::
              (  0 <= i₂₂₃
                && 0 <= i₂₂₃
                && i₂₂₃ < i₈
                 ==> a[i₂₂₃] < a[m₂₂₄]
                    && i₂₂₃ < alength
                    && 0 <= i₂₂₃
                    && b₆[i₂₂₃] == a[i₂₂₃]
                  ||   (a[i₂₂₃] < a[m₂₂₄]
                       ==> false)
                    && i₂₂₃ < alength
                    && 0 <= i₂₂₃
                    && b₆[i₂₂₃] == a[m₂₂₄]))
        && i₈ < alength
        && 0 <= i₂
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] < a[m₇]
          || a[i₂] < a[m₁]
          || b₆[i₈ := a[m₇]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₂₈₅: int, i₂₈₄: int ::
              (  0 <= i₂₈₄
                && 0 <= i₂₈₄
                && i₂₈₄ < i₈
                 ==> a[i₂₈₄] < a[m₂₈₅]
                    && i₂₈₄ < alength
                    && 0 <= i₂₈₄
                    && b₆[i₂₈₄] == a[i₂₈₄]
                  ||   (a[i₂₈₄] < a[m₂₈₅]
                       ==> false)
                    && i₂₈₄ < alength
                    && 0 <= i₂₈₄
                    && b₆[i₂₈₄] == a[m₂₈₅]))
        && i₈ < alength
        && 0 <= i₂
        && 0 <= i₂
        && i₂ < i₈ + 1
        && a[i₂] < a[m₁]
         ==> a[i₈] < a[m₇]
          || b₆[i₈ := a[m₇]][i₂] == a[i₂]));

goal (forall a: [int]int, alength: int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₃₀₆: int, i₃₀₅: int ::
              (  0 <= i₃₀₅
                && 0 <= i₃₀₅
                && i₃₀₅ < i₈
                 ==> a[i₃₀₅] < a[m₃₀₆]
                    && i₃₀₅ < alength
                    && 0 <= i₃₀₅
                    && b₆[i₃₀₅] == a[i₃₀₅]
                  ||   (a[i₃₀₅] < a[m₃₀₆]
                       ==> false)
                    && i₃₀₅ < alength
                    && 0 <= i₃₀₅
                    && b₆[i₃₀₅] == a[m₃₀₆]))
        && i₈ < alength
        && 0 <= i₂
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] < a[m₇]
          || b₆[i₈ := a[m₇]][i₂] == a[i₂]
          || b₆[i₈ := a[m₇]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b₆: [int]int, i₈: int, j: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= i₂
                && i₂ < i₈
                 ==> a[i₂] < a[m₁]
                    && i₂ < alength
                    && 0 <= i₂
                    && b₆[i₂] == a[i₂]
                  ||   (a[i₂] < a[m₁]
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && b₆[i₂] == a[m₁]))
        && 0 <= alength
         ==> i₈ < alength
          || (exists k: int ::
                (  0 <= j
                  && j < alength
                   ==> 0 <= k
                    && k < j
                    && b₆[j] == a[k]))));

