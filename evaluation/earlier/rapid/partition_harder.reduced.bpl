goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                 ==> 0 <= clength₁
                    && clength₁ < clength₉
                    && 0 <= i₂
                    && i₂ < i₁₀
                    && 0 <= blength₃
                    && blength₃ < blength₁₂
                  ||   b₁₁[blength₃] == b[blength₃]
                    && c₁₃[clength₁] == c[clength₁]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
         ==> clength₉ + 0 == i₁₀ + 1 + 0));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                 ==> 0 <= clength₁
                    && clength₁ < clength₉
                    && 0 <= i₂
                    && i₂ < i₁₀
                    && 0 <= blength₃
                    && blength₃ < blength₁₂
                  ||   b₁₁[blength₃] == b[blength₃]
                    && c₁₃[clength₁] == c[clength₁]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
         ==> clength₉ + 0 == 0 + blength₁₂ + 1));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁₈₈: int, i₁₈₇: int, blength₁₈₆: int ::
              (  clength₁₈₈ + clength₁₈₈ == i₁₈₇ + i₁₈₇
                && clength₁₈₈ + clength₁₈₈ == blength₁₈₆ + blength₁₈₆
                && 0 <= clength₁₈₈
                && clength₁₈₈ < clength₉
                && 0 <= i₁₈₇
                && i₁₈₇ < i₁₀
                && 0 <= blength₁₈₆
                && blength₁₈₆ < blength₁₂
                 ==> a[i₁₈₇] >= 0
                    && i₁₈₇ < alength
                    && b₁₁[blength₁₈₆] == a[i₁₈₇]
                  ||   (a[i₁₈₇] >= 0
                       ==> false)
                    && i₁₈₇ < alength
                    && c₁₃[clength₁₈₈] == a[i₁₈₇]))
        && (forall clength₁₉₁: int, i₁₉₀: int, blength₁₈₉: int ::
              (  clength₁₉₁ + clength₁₉₁ == i₁₉₀ + i₁₉₀
                && clength₁₉₁ + clength₁₉₁ == blength₁₈₉ + blength₁₈₉
                 ==> 0 <= clength₁₉₁
                    && clength₁₉₁ < clength₉
                    && 0 <= i₁₉₀
                    && i₁₉₀ < i₁₀
                    && 0 <= blength₁₈₉
                    && blength₁₈₉ < blength₁₂
                  ||   b₁₁[blength₁₈₉] == b[blength₁₈₉]
                    && c₁₃[clength₁₉₁] == c[clength₁₉₁]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
        && clength₁ + clength₁ == i₂ + i₂
        && clength₁ + clength₁ == blength₃ + blength₃
         ==> clength₁ < clength₉
          || b₁₁[blength₁₂ := a[i₁₀]][blength₃] == b[blength₃]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                 ==> 0 <= clength₁
                    && clength₁ < clength₉
                    && 0 <= i₂
                    && i₂ < i₁₀
                    && 0 <= blength₃
                    && blength₃ < blength₁₂
                  ||   b₁₁[blength₃] == b[blength₃]
                    && c₁₃[clength₁] == c[clength₁]))
        && i₁₀ < alength
         ==> a[i₁₀] >= 0
          || clength₉ + 1 + 0 == 0 + blength₁₂));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₀₇: int, i₄₀₆: int, blength₄₀₅: int ::
              (  clength₄₀₇ + clength₄₀₇ == i₄₀₆ + i₄₀₆
                && clength₄₀₇ + clength₄₀₇ == blength₄₀₅ + blength₄₀₅
                && 0 <= clength₄₀₇
                && clength₄₀₇ < clength₉
                && 0 <= i₄₀₆
                && i₄₀₆ < i₁₀
                && 0 <= blength₄₀₅
                && blength₄₀₅ < blength₁₂
                 ==> a[i₄₀₆] >= 0
                    && i₄₀₆ < alength
                    && b₁₁[blength₄₀₅] == a[i₄₀₆]
                  ||   (a[i₄₀₆] >= 0
                       ==> false)
                    && i₄₀₆ < alength
                    && c₁₃[clength₄₀₇] == a[i₄₀₆]))
        && (forall clength₄₁₀: int, i₄₀₉: int, blength₄₀₈: int ::
              (  clength₄₁₀ + clength₄₁₀ == i₄₀₉ + i₄₀₉
                && clength₄₁₀ + clength₄₁₀ == blength₄₀₈ + blength₄₀₈
                 ==> 0 <= clength₄₁₀
                    && clength₄₁₀ < clength₉
                    && 0 <= i₄₀₉
                    && i₄₀₉ < i₁₀
                    && 0 <= blength₄₀₈
                    && blength₄₀₈ < blength₁₂
                  ||   b₁₁[blength₄₀₈] == b[blength₄₀₈]
                    && c₁₃[clength₄₁₀] == c[clength₄₁₀]))
        && i₁₀ < alength
        && clength₁ + clength₁ == i₂ + i₂
        && clength₁ + clength₁ == blength₃ + blength₃
         ==> clength₁ < clength₉ + 1
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₃₇: int, i₄₃₆: int, blength₄₃₅: int ::
              (  clength₄₃₇ + clength₄₃₇ == i₄₃₆ + i₄₃₆
                && clength₄₃₇ + clength₄₃₇ == blength₄₃₅ + blength₄₃₅
                && 0 <= clength₄₃₇
                && clength₄₃₇ < clength₉
                && 0 <= i₄₃₆
                && i₄₃₆ < i₁₀
                && 0 <= blength₄₃₅
                && blength₄₃₅ < blength₁₂
                 ==> a[i₄₃₆] >= 0
                    && i₄₃₆ < alength
                    && b₁₁[blength₄₃₅] == a[i₄₃₆]
                  ||   (a[i₄₃₆] >= 0
                       ==> false)
                    && i₄₃₆ < alength
                    && c₁₃[clength₄₃₇] == a[i₄₃₆]))
        && (forall clength₄₄₀: int, i₄₃₉: int, blength₄₃₈: int ::
              (  clength₄₄₀ + clength₄₄₀ == i₄₃₉ + i₄₃₉
                && clength₄₄₀ + clength₄₄₀ == blength₄₃₈ + blength₄₃₈
                 ==> 0 <= clength₄₄₀
                    && clength₄₄₀ < clength₉
                    && 0 <= i₄₃₉
                    && i₄₃₉ < i₁₀
                    && 0 <= blength₄₃₈
                    && blength₄₃₈ < blength₁₂
                  ||   b₁₁[blength₄₃₈] == b[blength₄₃₈]
                    && c₁₃[clength₄₄₀] == c[clength₄₄₀]))
        && i₁₀ < alength
        && clength₁ + clength₁ == i₂ + i₂
        && clength₁ + clength₁ == blength₃ + blength₃
         ==> 0 <= i₂
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₆₇: int, i₄₆₆: int, blength₄₆₅: int ::
              (  clength₄₆₇ + clength₄₆₇ == i₄₆₆ + i₄₆₆
                && clength₄₆₇ + clength₄₆₇ == blength₄₆₅ + blength₄₆₅
                && 0 <= clength₄₆₇
                && clength₄₆₇ < clength₉
                && 0 <= i₄₆₆
                && i₄₆₆ < i₁₀
                && 0 <= blength₄₆₅
                && blength₄₆₅ < blength₁₂
                 ==> a[i₄₆₆] >= 0
                    && i₄₆₆ < alength
                    && b₁₁[blength₄₆₅] == a[i₄₆₆]
                  ||   (a[i₄₆₆] >= 0
                       ==> false)
                    && i₄₆₆ < alength
                    && c₁₃[clength₄₆₇] == a[i₄₆₆]))
        && (forall clength₄₇₀: int, i₄₆₉: int, blength₄₆₈: int ::
              (  clength₄₇₀ + clength₄₇₀ == i₄₆₉ + i₄₆₉
                && clength₄₇₀ + clength₄₇₀ == blength₄₆₈ + blength₄₆₈
                 ==> 0 <= clength₄₇₀
                    && clength₄₇₀ < clength₉
                    && 0 <= i₄₆₉
                    && i₄₆₉ < i₁₀
                    && 0 <= blength₄₆₈
                    && blength₄₆₈ < blength₁₂
                  ||   b₁₁[blength₄₆₈] == b[blength₄₆₈]
                    && c₁₃[clength₄₇₀] == c[clength₄₇₀]))
        && i₁₀ < alength
        && clength₁ + clength₁ == i₂ + i₂
        && clength₁ + clength₁ == blength₃ + blength₃
         ==> i₂ < i₁₀ + 1
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₉₇: int, i₄₉₆: int, blength₄₉₅: int ::
              (  clength₄₉₇ + clength₄₉₇ == i₄₉₆ + i₄₉₆
                && clength₄₉₇ + clength₄₉₇ == blength₄₉₅ + blength₄₉₅
                && 0 <= clength₄₉₇
                && clength₄₉₇ < clength₉
                && 0 <= i₄₉₆
                && i₄₉₆ < i₁₀
                && 0 <= blength₄₉₅
                && blength₄₉₅ < blength₁₂
                 ==> a[i₄₉₆] >= 0
                    && i₄₉₆ < alength
                    && b₁₁[blength₄₉₅] == a[i₄₉₆]
                  ||   (a[i₄₉₆] >= 0
                       ==> false)
                    && i₄₉₆ < alength
                    && c₁₃[clength₄₉₇] == a[i₄₉₆]))
        && (forall clength₅₀₀: int, i₄₉₉: int, blength₄₉₈: int ::
              (  clength₅₀₀ + clength₅₀₀ == i₄₉₉ + i₄₉₉
                && clength₅₀₀ + clength₅₀₀ == blength₄₉₈ + blength₄₉₈
                 ==> 0 <= clength₅₀₀
                    && clength₅₀₀ < clength₉
                    && 0 <= i₄₉₉
                    && i₄₉₉ < i₁₀
                    && 0 <= blength₄₉₈
                    && blength₄₉₈ < blength₁₂
                  ||   b₁₁[blength₄₉₈] == b[blength₄₉₈]
                    && c₁₃[clength₅₀₀] == c[clength₅₀₀]))
        && i₁₀ < alength
        && clength₁ + clength₁ == i₂ + i₂
        && clength₁ + clength₁ == blength₃ + blength₃
         ==> 0 <= blength₃
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₅₂₇: int, i₅₂₆: int, blength₅₂₅: int ::
              (  clength₅₂₇ + clength₅₂₇ == i₅₂₆ + i₅₂₆
                && clength₅₂₇ + clength₅₂₇ == blength₅₂₅ + blength₅₂₅
                && 0 <= clength₅₂₇
                && clength₅₂₇ < clength₉
                && 0 <= i₅₂₆
                && i₅₂₆ < i₁₀
                && 0 <= blength₅₂₅
                && blength₅₂₅ < blength₁₂
                 ==> a[i₅₂₆] >= 0
                    && i₅₂₆ < alength
                    && b₁₁[blength₅₂₅] == a[i₅₂₆]
                  ||   (a[i₅₂₆] >= 0
                       ==> false)
                    && i₅₂₆ < alength
                    && c₁₃[clength₅₂₇] == a[i₅₂₆]))
        && (forall clength₅₃₀: int, i₅₂₉: int, blength₅₂₈: int ::
              (  clength₅₃₀ + clength₅₃₀ == i₅₂₉ + i₅₂₉
                && clength₅₃₀ + clength₅₃₀ == blength₅₂₈ + blength₅₂₈
                 ==> 0 <= clength₅₃₀
                    && clength₅₃₀ < clength₉
                    && 0 <= i₅₂₉
                    && i₅₂₉ < i₁₀
                    && 0 <= blength₅₂₈
                    && blength₅₂₈ < blength₁₂
                  ||   b₁₁[blength₅₂₈] == b[blength₅₂₈]
                    && c₁₃[clength₅₃₀] == c[clength₅₃₀]))
        && i₁₀ < alength
        && clength₁ + clength₁ == i₂ + i₂
        && clength₁ + clength₁ == blength₃ + blength₃
         ==> blength₃ < blength₁₂
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal {:named "ensures"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                 ==> 0 <= clength₁
                    && clength₁ < clength₉
                    && 0 <= i₂
                    && i₂ < i₁₀
                    && 0 <= blength₃
                    && blength₃ < blength₁₂
                  ||   b₁₁[blength₃] == b[blength₃]
                    && c₁₃[clength₁] == c[clength₁]))
        && 0 <= alength
        && 0 <= pos
        && pos < blength₁₂
         ==> i₁₀ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < alength
                  && b₁₁[pos] == a[pos2])));

goal {:named "ensures"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && clength₁ + clength₁ == blength₃ + blength₃
                 ==> 0 <= clength₁
                    && clength₁ < clength₉
                    && 0 <= i₂
                    && i₂ < i₁₀
                    && 0 <= blength₃
                    && blength₃ < blength₁₂
                  ||   b₁₁[blength₃] == b[blength₃]
                    && c₁₃[clength₁] == c[clength₁]))
        && 0 <= alength
        && 0 <= pos
        && pos < clength₉
         ==> i₁₀ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < alength
                  && c₁₃[pos] == a[pos2])));

