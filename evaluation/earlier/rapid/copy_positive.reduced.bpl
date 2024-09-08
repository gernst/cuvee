goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && i₈ <= blength
        && (forall alength₁₇₆: int, i₁₇₇: int ::
              (  0 <= alength₁₇₆
                && alength₁₇₆ < alength₇
                && 0 <= i₁₇₇
                && i₁₇₇ < i₈
                 ==> b[i₁₇₇] >= 0
                    && i₁₇₇ < blength
                    && 0 <= i₁₇₇
                    && a₆[alength₁₇₆] == b[i₁₇₇]
                  ||   (b[i₁₇₇] >= 0
                       ==> false)
                    && i₁₇₇ < blength
                    && 0 <= i₁₇₇))
        && (forall alength₁₇₈: int, i₁₇₉: int ::
                  0 <= alength₁₇₈
                  && alength₁₇₈ < alength₇
                  && 0 <= i₁₇₉
                  && i₁₇₉ < i₈
                || a₆[alength₁₇₈] == a[alength₁₇₈])
        && i₈ < blength
        && b[i₈] >= 0
        && 0 <= alength₁
        && alength₁ < alength₇ + 1
        && 0 <= i₂
        && i₂ < i₈ + 1
        && b[i₂] >= 0
         ==> a₆[alength₇ := b[i₈]][alength₁] == b[i₂]));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && i₈ <= blength
        && (forall alength₂₁₈: int, i₂₁₉: int ::
              (  0 <= alength₂₁₈
                && alength₂₁₈ < alength₇
                && 0 <= i₂₁₉
                && i₂₁₉ < i₈
                 ==> b[i₂₁₉] >= 0
                    && i₂₁₉ < blength
                    && 0 <= i₂₁₉
                    && a₆[alength₂₁₈] == b[i₂₁₉]
                  ||   (b[i₂₁₉] >= 0
                       ==> false)
                    && i₂₁₉ < blength
                    && 0 <= i₂₁₉))
        && (forall alength₂₂₀: int, i₂₂₁: int ::
                  0 <= alength₂₂₀
                  && alength₂₂₀ < alength₇
                  && 0 <= i₂₂₁
                  && i₂₂₁ < i₈
                || a₆[alength₂₂₀] == a[alength₂₂₀])
        && i₈ < blength
        && b[i₈] >= 0
         ==> 0 <= i₂
          || a₆[alength₇ := b[i₈]][alength₁] == a[alength₁]));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && i₈ <= blength
        && (forall alength₂₃₀: int, i₂₃₁: int ::
              (  0 <= alength₂₃₀
                && alength₂₃₀ < alength₇
                && 0 <= i₂₃₁
                && i₂₃₁ < i₈
                 ==> b[i₂₃₁] >= 0
                    && i₂₃₁ < blength
                    && 0 <= i₂₃₁
                    && a₆[alength₂₃₀] == b[i₂₃₁]
                  ||   (b[i₂₃₁] >= 0
                       ==> false)
                    && i₂₃₁ < blength
                    && 0 <= i₂₃₁))
        && (forall alength₂₃₂: int, i₂₃₃: int ::
                  0 <= alength₂₃₂
                  && alength₂₃₂ < alength₇
                  && 0 <= i₂₃₃
                  && i₂₃₃ < i₈
                || a₆[alength₂₃₂] == a[alength₂₃₂])
        && i₈ < blength
        && b[i₈] >= 0
         ==> i₂ < i₈ + 1
          || a₆[alength₇ := b[i₈]][alength₁] == a[alength₁]));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, k: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && i₈ <= blength
        && (forall alength₁: int, i₂: int ::
              (  0 <= alength₁
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
        && (forall alength₁: int, i₂: int ::
                  0 <= alength₁
                  && alength₁ < alength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || a₆[alength₁] == a[alength₁])
        && 0 <= k
        && k < alength₇
        && 0 <= blength
         ==> i₈ < blength
          || 0 <= a₆[k]));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, k: int ::
      (  0 <= blength
        && 0 <= i₈
        && 0 <= alength₇
        && 0 <= i₈
        && i₈ <= blength
        && (forall alength₁: int, i₂: int ::
              (  0 <= alength₁
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
        && (forall alength₁: int, i₂: int ::
                  0 <= alength₁
                  && alength₁ < alength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || a₆[alength₁] == a[alength₁])
         ==> i₈ < blength
          || (exists l: int ::
                (  0 <= k
                  && k < alength₇
                  && 0 <= blength
                   ==> a₆[k] == b[l]))));

