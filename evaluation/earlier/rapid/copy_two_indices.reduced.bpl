goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, i₇: int, j₈: int, i₁: int, j₂: int ::
      (  0 <= blength
        && 0 <= i₇
        && i₇ == j₈
        && 0 <= i₇
        && 0 <= j₈
        && i₇ <= blength
        && (forall i₉₂: int, j₉₁: int ::
              (  0 <= i₉₂
                && i₉₂ < i₇
                && 0 <= j₉₁
                && j₉₁ < j₈
                 ==> i₉₂ < blength
                  && 0 <= i₉₂
                  && i₉₂ == j₉₁
                  && a₆[i₉₂] == b[j₉₁]))
        && (forall i₉₄: int, j₉₃: int ::
                  0 <= i₉₄
                  && i₉₄ < i₇
                  && 0 <= j₉₃
                  && j₉₃ < j₈
                || a₆[i₉₄] == a[i₉₄])
        && i₇ < blength
        && 0 <= i₁
        && i₁ < i₇ + 1
        && 0 <= j₂
        && j₂ < j₈ + 1
         ==> i₁ == j₂));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, i₇: int, j₈: int, i₁: int, j₂: int ::
      (  0 <= blength
        && 0 <= i₇
        && i₇ == j₈
        && 0 <= i₇
        && 0 <= j₈
        && i₇ <= blength
        && (forall i₁₀₄: int, j₁₀₃: int ::
              (  0 <= i₁₀₄
                && i₁₀₄ < i₇
                && 0 <= j₁₀₃
                && j₁₀₃ < j₈
                 ==> i₁₀₄ < blength
                  && 0 <= i₁₀₄
                  && i₁₀₄ == j₁₀₃
                  && a₆[i₁₀₄] == b[j₁₀₃]))
        && (forall i₁₀₆: int, j₁₀₅: int ::
                  0 <= i₁₀₆
                  && i₁₀₆ < i₇
                  && 0 <= j₁₀₅
                  && j₁₀₅ < j₈
                || a₆[i₁₀₆] == a[i₁₀₆])
        && i₇ < blength
        && 0 <= i₁
        && i₁ < i₇ + 1
        && 0 <= j₂
        && j₂ < j₈ + 1
         ==> a₆[i₇ := b[j₈]][i₁] == b[j₂]));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, i₇: int, j₈: int, i₁: int, j₂: int ::
      (  0 <= blength
        && 0 <= i₇
        && i₇ == j₈
        && 0 <= i₇
        && 0 <= j₈
        && i₇ <= blength
        && (forall i₁₃₀: int, j₁₂₉: int ::
              (  0 <= i₁₃₀
                && i₁₃₀ < i₇
                && 0 <= j₁₂₉
                && j₁₂₉ < j₈
                 ==> i₁₃₀ < blength
                  && 0 <= i₁₃₀
                  && i₁₃₀ == j₁₂₉
                  && a₆[i₁₃₀] == b[j₁₂₉]))
        && (forall i₁₃₂: int, j₁₃₁: int ::
                  0 <= i₁₃₂
                  && i₁₃₂ < i₇
                  && 0 <= j₁₃₁
                  && j₁₃₁ < j₈
                || a₆[i₁₃₂] == a[i₁₃₂])
        && i₇ < blength
         ==> 0 <= j₂
          || a₆[i₇ := b[j₈]][i₁] == a[i₁]));

goal (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, i₇: int, j₈: int, i₁: int, j₂: int ::
      (  0 <= blength
        && 0 <= i₇
        && i₇ == j₈
        && 0 <= i₇
        && 0 <= j₈
        && i₇ <= blength
        && (forall i₁₄₂: int, j₁₄₁: int ::
              (  0 <= i₁₄₂
                && i₁₄₂ < i₇
                && 0 <= j₁₄₁
                && j₁₄₁ < j₈
                 ==> i₁₄₂ < blength
                  && 0 <= i₁₄₂
                  && i₁₄₂ == j₁₄₁
                  && a₆[i₁₄₂] == b[j₁₄₁]))
        && (forall i₁₄₄: int, j₁₄₃: int ::
                  0 <= i₁₄₄
                  && i₁₄₄ < i₇
                  && 0 <= j₁₄₃
                  && j₁₄₃ < j₈
                || a₆[i₁₄₄] == a[i₁₄₄])
        && i₇ < blength
         ==> j₂ < j₈ + 1
          || a₆[i₇ := b[j₈]][i₁] == a[i₁]));

