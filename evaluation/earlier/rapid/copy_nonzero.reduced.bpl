goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && (forall alength₁₇₁: int, i₁₇₂: int ::
              (  0 <= i₁₇₂
                && 0 <= alength₁₇₁
                && alength₁₇₁ < alength₇
                && 0 <= i₁₇₂
                && i₁₇₂ < i₈
                 ==> (b[i₁₇₂] == 0
                       ==> false)
                    && i₁₇₂ < blength
                    && 0 <= i₁₇₂
                    && a₆[alength₁₇₁] == b[i₁₇₂]
                  ||   b[i₁₇₂] == 0
                    && i₁₇₂ < blength
                    && 0 <= i₁₇₂))
        && (forall alength₁₇₃: int, i₁₇₄: int ::
              (0 <= i₁₇₄
                 ==> 0 <= alength₁₇₃
                    && alength₁₇₃ < alength₇
                    && 0 <= i₁₇₄
                    && i₁₇₄ < i₈
                  || a₆[alength₁₇₃] == a[alength₁₇₃]))
        && i₈ < blength
        && 0 <= i₂
        && 0 <= alength₁
        && alength₁ < alength₇ + 1
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> b[i₈] == 0
          || a₆[alength₇ := b[i₈]][alength₁] == b[i₂]
          || b[i₂] == 0));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && (forall alength₂₂₃: int, i₂₂₄: int ::
              (  0 <= i₂₂₄
                && 0 <= alength₂₂₃
                && alength₂₂₃ < alength₇
                && 0 <= i₂₂₄
                && i₂₂₄ < i₈
                 ==> (b[i₂₂₄] == 0
                       ==> false)
                    && i₂₂₄ < blength
                    && 0 <= i₂₂₄
                    && a₆[alength₂₂₃] == b[i₂₂₄]
                  ||   b[i₂₂₄] == 0
                    && i₂₂₄ < blength
                    && 0 <= i₂₂₄))
        && (forall alength₂₂₅: int, i₂₂₆: int ::
              (0 <= i₂₂₆
                 ==> 0 <= alength₂₂₅
                    && alength₂₂₅ < alength₇
                    && 0 <= i₂₂₆
                    && i₂₂₆ < i₈
                  || a₆[alength₂₂₅] == a[alength₂₂₅]))
        && i₈ < blength
        && 0 <= i₂
         ==> i₂ < i₈ + 1
          || b[i₈] == 0
          || a₆[alength₇ := b[i₈]][alength₁] == a[alength₁]));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, k: int ::
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
                 ==> (b[i₂] == 0
                       ==> false)
                    && i₂ < blength
                    && 0 <= i₂
                    && a₆[alength₁] == b[i₂]
                  ||   b[i₂] == 0
                    && i₂ < blength
                    && 0 <= i₂))
        && (forall alength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= alength₁
                    && alength₁ < alength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || a₆[alength₁] == a[alength₁]))
        && 0 <= blength
        && 0 <= k
        && k < alength₇
        && a₆[k] == 0
         ==> i₈ < blength));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, k: int ::
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
                 ==> (b[i₂] == 0
                       ==> false)
                    && i₂ < blength
                    && 0 <= i₂
                    && a₆[alength₁] == b[i₂]
                  ||   b[i₂] == 0
                    && i₂ < blength
                    && 0 <= i₂))
        && (forall alength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= alength₁
                    && alength₁ < alength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || a₆[alength₁] == a[alength₁]))
         ==> i₈ < blength
          || (exists l: int ::
                (  0 <= k
                  && 0 <= blength
                  && k < alength₇
                   ==> a₆[k] == b[l]))));

