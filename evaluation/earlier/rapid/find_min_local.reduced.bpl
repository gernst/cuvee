goal (forall a: [int]int, alength: int, b: [int]int, b₉: [int]int, blength₁₀: int, m₁₁: int, i₁₂: int, x₄: int, i₃: int ::
      (  0 <= alength
        && 0 <= i₁₂
        && 1 <= blength₁₀
        && 0 <= i₁₂
        && i₁₂ <= alength
        && (forall x₁₁₃: int, i₁₁₄: int ::
              (  x₁₁₃ == i₁₁₄
                && 0 <= i₁₁₄
                && i₁₁₄ < i₁₂
                 ==> (exists m₂: int, i₁₁₅: int ::
                        a[i₁₁₅] < a[m₂]
                        && i₁₁₅ < alength
                        && 0 <= i₁₁₅
                        && x₁₁₃ == i₁₁₅
                        && 0 <= i₁₁₅
                        && i₁₁₅ < i₁₂
                        && b₉[x₁₁₃] == a[i₁₁₅])))
        && (forall x₁₁₆: int ::
                (exists i₁₁₇: int ::
                        x₁₁₆ == i₁₁₇
                        && 0 <= i₁₁₇
                        && i₁₁₇ < i₁₂)
                || b₉[x₁₁₆] == b[0 := a[0]][x₁₁₆])
        && (forall blength₁: int, i₁₁₈: int ::
              (  0 <= i₁₁₈
                && blength₁ <= blength₁
                && i₁₁₈ <= i₁₁₈
                && 1 <= blength₁
                && blength₁ < blength₁₀
                && 0 <= i₁₁₈
                && i₁₁₈ < i₁₂
                 ==> i₁₁₈ < alength))
        && i₁₂ < alength
        && x₄ == i₃
        && 0 <= i₃
        && i₃ < i₁₂ + 1
         ==> a[i₁₂] < a[m₁₁]
          || (exists m₂: int, i₁₁₉: int ::
                  a[i₁₁₉] < a[m₂]
                  && i₁₁₉ < alength
                  && 0 <= i₁₁₉
                  && x₄ == i₁₁₉
                  && 0 <= i₁₁₉
                  && i₁₁₉ < i₁₂ + 1
                  && b₉[x₄] == a[i₁₁₉])));

goal (forall a: [int]int, alength: int, b: [int]int, b₉: [int]int, blength₁₀: int, i₁₂: int, j: int ::
      (  0 <= alength
        && 0 <= i₁₂
        && 1 <= blength₁₀
        && 0 <= i₁₂
        && i₁₂ <= alength
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 0 <= i₃
                && i₃ < i₁₂
                 ==> (exists m₂: int, i₃: int ::
                        a[i₃] < a[m₂]
                        && i₃ < alength
                        && 0 <= i₃
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₂
                        && b₉[x₄] == a[i₃])))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₂)
                || b₉[x₄] == b[0 := a[0]][x₄])
        && (forall blength₁: int, i₃: int ::
              (  0 <= i₃
                && blength₁ <= blength₁
                && i₃ <= i₃
                && 1 <= blength₁
                && blength₁ < blength₁₀
                && 0 <= i₃
                && i₃ < i₁₂
                 ==> i₃ < alength))
         ==> i₁₂ < alength
          || (exists k: int ::
                (  1 <= alength
                  && 0 <= j
                  && j < blength₁₀
                   ==> 0 <= k
                    && k < alength
                    && b₉[j] == a[k]))));

goal (forall a: [int]int, alength: int, b: [int]int, b₉: [int]int, blength₁₀: int, i₁₂: int, j: int, k: int ::
      (  0 <= alength
        && 0 <= i₁₂
        && 1 <= blength₁₀
        && 0 <= i₁₂
        && i₁₂ <= alength
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 0 <= i₃
                && i₃ < i₁₂
                 ==> (exists m₂: int, i₃: int ::
                        a[i₃] < a[m₂]
                        && i₃ < alength
                        && 0 <= i₃
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₂
                        && b₉[x₄] == a[i₃])))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₂)
                || b₉[x₄] == b[0 := a[0]][x₄])
        && (forall blength₁: int, i₃: int ::
              (  0 <= i₃
                && blength₁ <= blength₁
                && i₃ <= i₃
                && 1 <= blength₁
                && blength₁ < blength₁₀
                && 0 <= i₃
                && i₃ < i₁₂
                 ==> i₃ < alength))
        && 1 <= alength
        && 0 <= j
        && 0 <= k
        && j <= k
        && k < blength₁₀
         ==> i₁₂ < alength
          || b₉[k] <= b₉[j]));

