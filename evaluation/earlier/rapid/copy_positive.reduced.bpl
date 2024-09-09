goal (forall b: [int]int, blength: int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && (forall alength₁₄₃: int, i₁₄₄: int ::
              (  0 <= i₁₄₄
                && 0 <= alength₁₄₃
                && alength₁₄₃ < alength₇
                && 0 <= i₁₄₄
                && i₁₄₄ < i₈
                 ==> b[i₁₄₄] >= 0
                    && i₁₄₄ < blength
                    && 0 <= i₁₄₄
                    && a₆[alength₁₄₃] == b[i₁₄₄]
                  ||   (b[i₁₄₄] >= 0
                       ==> false)
                    && i₁₄₄ < blength
                    && 0 <= i₁₄₄))
        && i₈ < blength
        && b[i₈] >= 0
        && 0 <= i₂
        && 0 <= alength₁
        && alength₁ < alength₇ + 1
        && 0 <= i₂
        && i₂ < i₈ + 1
        && b[i₂] >= 0
         ==> a₆[alength₇ := b[i₈]][alength₁] == b[i₂]));

goal (forall b: [int]int, blength: int, a₆: [int]int, alength₇: int, i₈: int, k: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && (forall alength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= alength₁
                && alength₁ < alength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> b[i₂] >= 0
                    && i₂ < blength
                    && 0 <= i₂
                    && a₆[alength₁] == b[i₂]
                  ||   (b[i₂] >= 0
                       ==> false)
                    && i₂ < blength
                    && 0 <= i₂))
        && 0 <= k
        && k < alength₇
        && 0 <= blength
         ==> i₈ < blength
          || 0 <= a₆[k]));

goal (forall b: [int]int, blength: int, a₆: [int]int, alength₇: int, i₈: int, k: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && (forall alength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= alength₁
                && alength₁ < alength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> b[i₂] >= 0
                    && i₂ < blength
                    && 0 <= i₂
                    && a₆[alength₁] == b[i₂]
                  ||   (b[i₂] >= 0
                       ==> false)
                    && i₂ < blength
                    && 0 <= i₂))
         ==> i₈ < blength
          || (exists l: int ::
                (  0 <= k
                  && k < alength₇
                  && 0 <= blength
                   ==> a₆[k] == b[l]))));

