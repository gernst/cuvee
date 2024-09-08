goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && i₈ == alength₇
        && alength₇ <= blength
        && 0 <= alength₇
        && 0 <= i₈
        && i₈ <= blength
        && (forall alength₁₀₀: int, i₁₀₁: int ::
              (  0 <= alength₁₀₀
                && alength₁₀₀ < alength₇
                && 0 <= i₁₀₁
                && i₁₀₁ < i₈
                 ==> i₁₀₁ < blength
                  && 0 <= i₁₀₁
                  && i₁₀₁ == alength₁₀₀
                  && alength₁₀₀ <= blength
                  && a₆[i₁₀₁] == b[i₁₀₁]))
        && (forall alength₁₀₂: int, i₁₀₃: int ::
                  0 <= alength₁₀₂
                  && alength₁₀₂ < alength₇
                  && 0 <= i₁₀₃
                  && i₁₀₃ < i₈
                || a₆[i₁₀₃] == a[i₁₀₃])
        && i₈ < blength
        && 0 <= alength₁
        && alength₁ < alength₇ + 1
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> i₂ == alength₁));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && i₈ == alength₇
        && alength₇ <= blength
        && 0 <= alength₇
        && 0 <= i₈
        && i₈ <= blength
        && (forall alength₁₂₈: int, i₁₂₉: int ::
              (  0 <= alength₁₂₈
                && alength₁₂₈ < alength₇
                && 0 <= i₁₂₉
                && i₁₂₉ < i₈
                 ==> i₁₂₉ < blength
                  && 0 <= i₁₂₉
                  && i₁₂₉ == alength₁₂₈
                  && alength₁₂₈ <= blength
                  && a₆[i₁₂₉] == b[i₁₂₉]))
        && (forall alength₁₃₀: int, i₁₃₁: int ::
                  0 <= alength₁₃₀
                  && alength₁₃₀ < alength₇
                  && 0 <= i₁₃₁
                  && i₁₃₁ < i₈
                || a₆[i₁₃₁] == a[i₁₃₁])
        && i₈ < blength
         ==> 0 <= alength₁
          || a₆[i₈ := b[i₈]][i₂] == a[i₂]));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, alength₁: int, i₂: int ::
      (  0 <= blength
        && 0 <= i₈
        && i₈ == alength₇
        && alength₇ <= blength
        && 0 <= alength₇
        && 0 <= i₈
        && i₈ <= blength
        && (forall alength₁₄₀: int, i₁₄₁: int ::
              (  0 <= alength₁₄₀
                && alength₁₄₀ < alength₇
                && 0 <= i₁₄₁
                && i₁₄₁ < i₈
                 ==> i₁₄₁ < blength
                  && 0 <= i₁₄₁
                  && i₁₄₁ == alength₁₄₀
                  && alength₁₄₀ <= blength
                  && a₆[i₁₄₁] == b[i₁₄₁]))
        && (forall alength₁₄₂: int, i₁₄₃: int ::
                  0 <= alength₁₄₂
                  && alength₁₄₂ < alength₇
                  && 0 <= i₁₄₃
                  && i₁₄₃ < i₈
                || a₆[i₁₄₃] == a[i₁₄₃])
        && i₈ < blength
         ==> alength₁ < alength₇ + 1
          || a₆[i₈ := b[i₈]][i₂] == a[i₂]));

