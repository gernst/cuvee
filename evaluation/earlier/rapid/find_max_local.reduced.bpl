goal (forall a: [int]int, alength: int, b: [int]int, b₉: [int]int, blength₁₀: int, m₁₁: int, i₁₂: int, x₄: int, i₃: int ::
      (  1 <= alength
        && 0 <= i₁₂
        && 1 <= blength₁₀
        && 1 <= i₁₂
        && i₁₂ <= alength
        && (forall x₁₂₇: int, i₁₂₈: int ::
              (  x₁₂₇ == i₁₂₈
                && 1 <= i₁₂₈
                && i₁₂₈ < i₁₂
                 ==> (exists m₂: int, i₁₂₉: int ::
                        a[i₁₂₉] > a[m₂]
                        && i₁₂₉ < alength
                        && 0 <= i₁₂₉
                        && x₁₂₇ == i₁₂₉
                        && 1 <= i₁₂₉
                        && i₁₂₉ < i₁₂
                        && b₉[x₁₂₇] == a[i₁₂₉])))
        && (forall x₁₃₀: int ::
                (exists i₁₃₁: int ::
                        x₁₃₀ == i₁₃₁
                        && 1 <= i₁₃₁
                        && i₁₃₁ < i₁₂)
                || b₉[x₁₃₀] == b[0 := a[0]][x₁₃₀])
        && (forall blength₁: int, i₁₃₂: int ::
              (  0 <= i₁₃₂
                && blength₁ <= blength₁
                && i₁₃₂ <= i₁₃₂
                && 1 <= blength₁
                && blength₁ < blength₁₀
                && 1 <= i₁₃₂
                && i₁₃₂ < i₁₂
                 ==> i₁₃₂ < alength))
        && i₁₂ < alength
        && x₄ == i₃
        && 1 <= i₃
        && i₃ < i₁₂ + 1
         ==> a[i₁₂] > a[m₁₁]
          || (exists m₂: int, i₁₃₃: int ::
                  a[i₁₃₃] > a[m₂]
                  && i₁₃₃ < alength
                  && 0 <= i₁₃₃
                  && x₄ == i₁₃₃
                  && 1 <= i₁₃₃
                  && i₁₃₃ < i₁₂ + 1
                  && b₉[x₄] == a[i₁₃₃])));

goal (forall a: [int]int, alength: int, b: [int]int, b₉: [int]int, blength₁₀: int, i₁₂: int, k: int ::
      (  1 <= alength
        && 0 <= i₁₂
        && 1 <= blength₁₀
        && 1 <= i₁₂
        && i₁₂ <= alength
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 1 <= i₃
                && i₃ < i₁₂
                 ==> (exists m₂: int, i₃: int ::
                        a[i₃] > a[m₂]
                        && i₃ < alength
                        && 0 <= i₃
                        && x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₂
                        && b₉[x₄] == a[i₃])))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₂)
                || b₉[x₄] == b[0 := a[0]][x₄])
        && (forall blength₁: int, i₃: int ::
              (  0 <= i₃
                && blength₁ <= blength₁
                && i₃ <= i₃
                && 1 <= blength₁
                && blength₁ < blength₁₀
                && 1 <= i₃
                && i₃ < i₁₂
                 ==> i₃ < alength))
        && 1 <= alength
        && 0 <= k
        && k < alength
        && (forall l: int ::
              (  0 <= l
                && l < k
                 ==> a[l] < a[k]))
         ==> i₁₂ < alength
          || (exists j: int ::
                  0 <= j
                  && j < blength₁₀
                  && a[k] == b₉[j])));

goal (forall a: [int]int, alength: int, b: [int]int, b₉: [int]int, blength₁₀: int, i₁₂: int, j: int ::
      (  1 <= alength
        && 0 <= i₁₂
        && 1 <= blength₁₀
        && 1 <= i₁₂
        && i₁₂ <= alength
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 1 <= i₃
                && i₃ < i₁₂
                 ==> (exists m₂: int, i₃: int ::
                        a[i₃] > a[m₂]
                        && i₃ < alength
                        && 0 <= i₃
                        && x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₂
                        && b₉[x₄] == a[i₃])))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₂)
                || b₉[x₄] == b[0 := a[0]][x₄])
        && (forall blength₁: int, i₃: int ::
              (  0 <= i₃
                && blength₁ <= blength₁
                && i₃ <= i₃
                && 1 <= blength₁
                && blength₁ < blength₁₀
                && 1 <= i₃
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
      (  1 <= alength
        && 0 <= i₁₂
        && 1 <= blength₁₀
        && 1 <= i₁₂
        && i₁₂ <= alength
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 1 <= i₃
                && i₃ < i₁₂
                 ==> (exists m₂: int, i₃: int ::
                        a[i₃] > a[m₂]
                        && i₃ < alength
                        && 0 <= i₃
                        && x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₂
                        && b₉[x₄] == a[i₃])))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₂)
                || b₉[x₄] == b[0 := a[0]][x₄])
        && (forall blength₁: int, i₃: int ::
              (  0 <= i₃
                && blength₁ <= blength₁
                && i₃ <= i₃
                && 1 <= blength₁
                && blength₁ < blength₁₀
                && 1 <= i₃
                && i₃ < i₁₂
                 ==> i₃ < alength))
        && 1 <= alength
        && 0 <= j
        && 0 <= k
        && j <= k
        && k < blength₁₀
         ==> i₁₂ < alength
          || b₉[j] <= b₉[k]));

