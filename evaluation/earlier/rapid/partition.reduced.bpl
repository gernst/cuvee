goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₂₃₈: int, i₂₃₇: int, blength₂₃₆: int ::
              (  0 <= i₂₃₇
                && 0 <= clength₂₃₈
                && clength₂₃₈ < clength₉
                && 0 <= i₂₃₇
                && i₂₃₇ < i₁₀
                && 0 <= blength₂₃₆
                && blength₂₃₆ < blength₁₂
                 ==> a[i₂₃₇] >= 0
                    && i₂₃₇ < alength
                    && 0 <= i₂₃₇
                    && b₁₁[blength₂₃₆] == a[i₂₃₇]
                  ||   (a[i₂₃₇] >= 0
                       ==> false)
                    && i₂₃₇ < alength
                    && 0 <= i₂₃₇
                    && c₁₃[clength₂₃₈] == a[i₂₃₇]))
        && (forall clength₂₄₁: int, i₂₄₀: int, blength₂₃₉: int ::
              (0 <= i₂₄₀
                 ==> 0 <= clength₂₄₁
                    && clength₂₄₁ < clength₉
                    && 0 <= i₂₄₀
                    && i₂₄₀ < i₁₀
                    && 0 <= blength₂₃₉
                    && blength₂₃₉ < blength₁₂
                  ||   b₁₁[blength₂₃₉] == b[blength₂₃₉]
                    && c₁₃[clength₂₄₁] == c[clength₂₄₁]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
        && 0 <= i₂
        && 0 <= clength₁
        && clength₁ < clength₉
        && 0 <= i₂
        && i₂ < i₁₀ + 1
        && 0 <= blength₃
        && blength₃ < blength₁₂ + 1
         ==> a[i₂] >= 0
          || c₁₃[clength₁] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₃₅₂: int, i₃₅₁: int, blength₃₅₀: int ::
              (  0 <= i₃₅₁
                && 0 <= clength₃₅₂
                && clength₃₅₂ < clength₉
                && 0 <= i₃₅₁
                && i₃₅₁ < i₁₀
                && 0 <= blength₃₅₀
                && blength₃₅₀ < blength₁₂
                 ==> a[i₃₅₁] >= 0
                    && i₃₅₁ < alength
                    && 0 <= i₃₅₁
                    && b₁₁[blength₃₅₀] == a[i₃₅₁]
                  ||   (a[i₃₅₁] >= 0
                       ==> false)
                    && i₃₅₁ < alength
                    && 0 <= i₃₅₁
                    && c₁₃[clength₃₅₂] == a[i₃₅₁]))
        && (forall clength₃₅₅: int, i₃₅₄: int, blength₃₅₃: int ::
              (0 <= i₃₅₄
                 ==> 0 <= clength₃₅₅
                    && clength₃₅₅ < clength₉
                    && 0 <= i₃₅₄
                    && i₃₅₄ < i₁₀
                    && 0 <= blength₃₅₃
                    && blength₃₅₃ < blength₁₂
                  ||   b₁₁[blength₃₅₃] == b[blength₃₅₃]
                    && c₁₃[clength₃₅₅] == c[clength₃₅₅]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
        && 0 <= i₂
        && 0 <= clength₁
        && clength₁ < clength₉
        && 0 <= i₂
        && i₂ < i₁₀ + 1
        && 0 <= blength₃
        && blength₃ < blength₁₂ + 1
        && a[i₂] >= 0
         ==> b₁₁[blength₁₂ := a[i₁₀]][blength₃] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₃₉₄: int, i₃₉₃: int, blength₃₉₂: int ::
              (  0 <= i₃₉₃
                && 0 <= clength₃₉₄
                && clength₃₉₄ < clength₉
                && 0 <= i₃₉₃
                && i₃₉₃ < i₁₀
                && 0 <= blength₃₉₂
                && blength₃₉₂ < blength₁₂
                 ==> a[i₃₉₃] >= 0
                    && i₃₉₃ < alength
                    && 0 <= i₃₉₃
                    && b₁₁[blength₃₉₂] == a[i₃₉₃]
                  ||   (a[i₃₉₃] >= 0
                       ==> false)
                    && i₃₉₃ < alength
                    && 0 <= i₃₉₃
                    && c₁₃[clength₃₉₄] == a[i₃₉₃]))
        && (forall clength₃₉₇: int, i₃₉₆: int, blength₃₉₅: int ::
              (0 <= i₃₉₆
                 ==> 0 <= clength₃₉₇
                    && clength₃₉₇ < clength₉
                    && 0 <= i₃₉₆
                    && i₃₉₆ < i₁₀
                    && 0 <= blength₃₉₅
                    && blength₃₉₅ < blength₁₂
                  ||   b₁₁[blength₃₉₅] == b[blength₃₉₅]
                    && c₁₃[clength₃₉₇] == c[clength₃₉₇]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
        && 0 <= i₂
        && 0 <= clength₁
        && clength₁ < clength₉
        && 0 <= i₂
        && i₂ < i₁₀ + 1
        && 0 <= blength₃
        && blength₃ < blength₁₂ + 1
         ==> b₁₁[blength₁₂ := a[i₁₀]][blength₃] == a[i₂]
          || c₁₃[clength₁] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₁₂: int, i₄₁₁: int, blength₄₁₀: int ::
              (  0 <= i₄₁₁
                && 0 <= clength₄₁₂
                && clength₄₁₂ < clength₉
                && 0 <= i₄₁₁
                && i₄₁₁ < i₁₀
                && 0 <= blength₄₁₀
                && blength₄₁₀ < blength₁₂
                 ==> a[i₄₁₁] >= 0
                    && i₄₁₁ < alength
                    && 0 <= i₄₁₁
                    && b₁₁[blength₄₁₀] == a[i₄₁₁]
                  ||   (a[i₄₁₁] >= 0
                       ==> false)
                    && i₄₁₁ < alength
                    && 0 <= i₄₁₁
                    && c₁₃[clength₄₁₂] == a[i₄₁₁]))
        && (forall clength₄₁₅: int, i₄₁₄: int, blength₄₁₃: int ::
              (0 <= i₄₁₄
                 ==> 0 <= clength₄₁₅
                    && clength₄₁₅ < clength₉
                    && 0 <= i₄₁₄
                    && i₄₁₄ < i₁₀
                    && 0 <= blength₄₁₃
                    && blength₄₁₃ < blength₁₂
                  ||   b₁₁[blength₄₁₃] == b[blength₄₁₃]
                    && c₁₃[clength₄₁₅] == c[clength₄₁₅]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
        && 0 <= i₂
         ==> 0 <= clength₁
          || b₁₁[blength₁₂ := a[i₁₀]][blength₃] == b[blength₃]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₄₁: int, i₄₄₀: int, blength₄₃₉: int ::
              (  0 <= i₄₄₀
                && 0 <= clength₄₄₁
                && clength₄₄₁ < clength₉
                && 0 <= i₄₄₀
                && i₄₄₀ < i₁₀
                && 0 <= blength₄₃₉
                && blength₄₃₉ < blength₁₂
                 ==> a[i₄₄₀] >= 0
                    && i₄₄₀ < alength
                    && 0 <= i₄₄₀
                    && b₁₁[blength₄₃₉] == a[i₄₄₀]
                  ||   (a[i₄₄₀] >= 0
                       ==> false)
                    && i₄₄₀ < alength
                    && 0 <= i₄₄₀
                    && c₁₃[clength₄₄₁] == a[i₄₄₀]))
        && (forall clength₄₄₄: int, i₄₄₃: int, blength₄₄₂: int ::
              (0 <= i₄₄₃
                 ==> 0 <= clength₄₄₄
                    && clength₄₄₄ < clength₉
                    && 0 <= i₄₄₃
                    && i₄₄₃ < i₁₀
                    && 0 <= blength₄₄₂
                    && blength₄₄₂ < blength₁₂
                  ||   b₁₁[blength₄₄₂] == b[blength₄₄₂]
                    && c₁₃[clength₄₄₄] == c[clength₄₄₄]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
        && 0 <= i₂
         ==> clength₁ < clength₉
          || b₁₁[blength₁₂ := a[i₁₀]][blength₃] == b[blength₃]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₄₉₀: int, blength₄₈₉: int ::
              (  0 <= i₄₉₀
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₄₉₀
                && i₄₉₀ < i₁₀
                && 0 <= blength₄₈₉
                && blength₄₈₉ < blength₁₂
                 ==> a[i₄₉₀] >= 0
                    && i₄₉₀ < alength
                    && 0 <= i₄₉₀
                    && b₁₁[blength₄₈₉] == a[i₄₉₀]
                  ||   (a[i₄₉₀] >= 0
                       ==> false)
                    && i₄₉₀ < alength
                    && 0 <= i₄₉₀
                    && c₁₃[clength₁] == a[i₄₉₀]))
        && (forall clength₁: int, i₄₉₂: int, blength₄₉₁: int ::
              (0 <= i₄₉₂
                 ==> 0 <= clength₁
                    && clength₁ < clength₉
                    && 0 <= i₄₉₂
                    && i₄₉₂ < i₁₀
                    && 0 <= blength₄₉₁
                    && blength₄₉₁ < blength₁₂
                  ||   b₁₁[blength₄₉₁] == b[blength₄₉₁]
                    && c₁₃[clength₁] == c[clength₁]))
        && i₁₀ < alength
        && a[i₁₀] >= 0
        && 0 <= i₂
         ==> i₂ < i₁₀ + 1
          || b₁₁[blength₁₂ := a[i₁₀]][blength₃] == b[blength₃]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₆₂₇: int, i₆₂₆: int, blength₆₂₅: int ::
              (  0 <= i₆₂₆
                && 0 <= clength₆₂₇
                && clength₆₂₇ < clength₉
                && 0 <= i₆₂₆
                && i₆₂₆ < i₁₀
                && 0 <= blength₆₂₅
                && blength₆₂₅ < blength₁₂
                 ==> a[i₆₂₆] >= 0
                    && i₆₂₆ < alength
                    && 0 <= i₆₂₆
                    && b₁₁[blength₆₂₅] == a[i₆₂₆]
                  ||   (a[i₆₂₆] >= 0
                       ==> false)
                    && i₆₂₆ < alength
                    && 0 <= i₆₂₆
                    && c₁₃[clength₆₂₇] == a[i₆₂₆]))
        && (forall clength₆₃₀: int, i₆₂₉: int, blength₆₂₈: int ::
              (0 <= i₆₂₉
                 ==> 0 <= clength₆₃₀
                    && clength₆₃₀ < clength₉
                    && 0 <= i₆₂₉
                    && i₆₂₉ < i₁₀
                    && 0 <= blength₆₂₈
                    && blength₆₂₈ < blength₁₂
                  ||   b₁₁[blength₆₂₈] == b[blength₆₂₈]
                    && c₁₃[clength₆₃₀] == c[clength₆₃₀]))
        && i₁₀ < alength
        && 0 <= i₂
        && 0 <= clength₁
        && clength₁ < clength₉ + 1
        && 0 <= i₂
        && i₂ < i₁₀ + 1
        && 0 <= blength₃
        && blength₃ < blength₁₂
         ==> a[i₁₀] >= 0
          || a[i₂] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₇₄₁: int, i₇₄₀: int, blength₇₃₉: int ::
              (  0 <= i₇₄₀
                && 0 <= clength₇₄₁
                && clength₇₄₁ < clength₉
                && 0 <= i₇₄₀
                && i₇₄₀ < i₁₀
                && 0 <= blength₇₃₉
                && blength₇₃₉ < blength₁₂
                 ==> a[i₇₄₀] >= 0
                    && i₇₄₀ < alength
                    && 0 <= i₇₄₀
                    && b₁₁[blength₇₃₉] == a[i₇₄₀]
                  ||   (a[i₇₄₀] >= 0
                       ==> false)
                    && i₇₄₀ < alength
                    && 0 <= i₇₄₀
                    && c₁₃[clength₇₄₁] == a[i₇₄₀]))
        && (forall clength₇₄₄: int, i₇₄₃: int, blength₇₄₂: int ::
              (0 <= i₇₄₃
                 ==> 0 <= clength₇₄₄
                    && clength₇₄₄ < clength₉
                    && 0 <= i₇₄₃
                    && i₇₄₃ < i₁₀
                    && 0 <= blength₇₄₂
                    && blength₇₄₂ < blength₁₂
                  ||   b₁₁[blength₇₄₂] == b[blength₇₄₂]
                    && c₁₃[clength₇₄₄] == c[clength₇₄₄]))
        && i₁₀ < alength
        && 0 <= i₂
        && 0 <= clength₁
        && clength₁ < clength₉ + 1
        && 0 <= i₂
        && i₂ < i₁₀ + 1
        && 0 <= blength₃
        && blength₃ < blength₁₂
        && a[i₂] >= 0
         ==> a[i₁₀] >= 0
          || b₁₁[blength₃] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₇₈₃: int, i₇₈₂: int, blength₇₈₁: int ::
              (  0 <= i₇₈₂
                && 0 <= clength₇₈₃
                && clength₇₈₃ < clength₉
                && 0 <= i₇₈₂
                && i₇₈₂ < i₁₀
                && 0 <= blength₇₈₁
                && blength₇₈₁ < blength₁₂
                 ==> a[i₇₈₂] >= 0
                    && i₇₈₂ < alength
                    && 0 <= i₇₈₂
                    && b₁₁[blength₇₈₁] == a[i₇₈₂]
                  ||   (a[i₇₈₂] >= 0
                       ==> false)
                    && i₇₈₂ < alength
                    && 0 <= i₇₈₂
                    && c₁₃[clength₇₈₃] == a[i₇₈₂]))
        && (forall clength₇₈₆: int, i₇₈₅: int, blength₇₈₄: int ::
              (0 <= i₇₈₅
                 ==> 0 <= clength₇₈₆
                    && clength₇₈₆ < clength₉
                    && 0 <= i₇₈₅
                    && i₇₈₅ < i₁₀
                    && 0 <= blength₇₈₄
                    && blength₇₈₄ < blength₁₂
                  ||   b₁₁[blength₇₈₄] == b[blength₇₈₄]
                    && c₁₃[clength₇₈₆] == c[clength₇₈₆]))
        && i₁₀ < alength
        && 0 <= i₂
        && 0 <= clength₁
        && clength₁ < clength₉ + 1
        && 0 <= i₂
        && i₂ < i₁₀ + 1
        && 0 <= blength₃
        && blength₃ < blength₁₂
         ==> a[i₁₀] >= 0
          || b₁₁[blength₃] == a[i₂]
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₈₇₈: int, i₈₇₇: int, blength₃: int ::
              (  0 <= i₈₇₇
                && 0 <= clength₈₇₈
                && clength₈₇₈ < clength₉
                && 0 <= i₈₇₇
                && i₈₇₇ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₈₇₇] >= 0
                    && i₈₇₇ < alength
                    && 0 <= i₈₇₇
                    && b₁₁[blength₃] == a[i₈₇₇]
                  ||   (a[i₈₇₇] >= 0
                       ==> false)
                    && i₈₇₇ < alength
                    && 0 <= i₈₇₇
                    && c₁₃[clength₈₇₈] == a[i₈₇₇]))
        && (forall clength₈₈₀: int, i₈₇₉: int, blength₃: int ::
              (0 <= i₈₇₉
                 ==> 0 <= clength₈₈₀
                    && clength₈₈₀ < clength₉
                    && 0 <= i₈₇₉
                    && i₈₇₉ < i₁₀
                    && 0 <= blength₃
                    && blength₃ < blength₁₂
                  ||   b₁₁[blength₃] == b[blength₃]
                    && c₁₃[clength₈₈₀] == c[clength₈₈₀]))
        && i₁₀ < alength
        && 0 <= i₂
         ==> i₂ < i₁₀ + 1
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₉₀₆: int, i₉₀₅: int, blength₉₀₄: int ::
              (  0 <= i₉₀₅
                && 0 <= clength₉₀₆
                && clength₉₀₆ < clength₉
                && 0 <= i₉₀₅
                && i₉₀₅ < i₁₀
                && 0 <= blength₉₀₄
                && blength₉₀₄ < blength₁₂
                 ==> a[i₉₀₅] >= 0
                    && i₉₀₅ < alength
                    && 0 <= i₉₀₅
                    && b₁₁[blength₉₀₄] == a[i₉₀₅]
                  ||   (a[i₉₀₅] >= 0
                       ==> false)
                    && i₉₀₅ < alength
                    && 0 <= i₉₀₅
                    && c₁₃[clength₉₀₆] == a[i₉₀₅]))
        && (forall clength₉₀₉: int, i₉₀₈: int, blength₉₀₇: int ::
              (0 <= i₉₀₈
                 ==> 0 <= clength₉₀₉
                    && clength₉₀₉ < clength₉
                    && 0 <= i₉₀₈
                    && i₉₀₈ < i₁₀
                    && 0 <= blength₉₀₇
                    && blength₉₀₇ < blength₁₂
                  ||   b₁₁[blength₉₀₇] == b[blength₉₀₇]
                    && c₁₃[clength₉₀₉] == c[clength₉₀₉]))
        && i₁₀ < alength
        && 0 <= i₂
         ==> 0 <= blength₃
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₉₃₅: int, i₉₃₄: int, blength₉₃₃: int ::
              (  0 <= i₉₃₄
                && 0 <= clength₉₃₅
                && clength₉₃₅ < clength₉
                && 0 <= i₉₃₄
                && i₉₃₄ < i₁₀
                && 0 <= blength₉₃₃
                && blength₉₃₃ < blength₁₂
                 ==> a[i₉₃₄] >= 0
                    && i₉₃₄ < alength
                    && 0 <= i₉₃₄
                    && b₁₁[blength₉₃₃] == a[i₉₃₄]
                  ||   (a[i₉₃₄] >= 0
                       ==> false)
                    && i₉₃₄ < alength
                    && 0 <= i₉₃₄
                    && c₁₃[clength₉₃₅] == a[i₉₃₄]))
        && (forall clength₉₃₈: int, i₉₃₇: int, blength₉₃₆: int ::
              (0 <= i₉₃₇
                 ==> 0 <= clength₉₃₈
                    && clength₉₃₈ < clength₉
                    && 0 <= i₉₃₇
                    && i₉₃₇ < i₁₀
                    && 0 <= blength₉₃₆
                    && blength₉₃₆ < blength₁₂
                  ||   b₁₁[blength₉₃₆] == b[blength₉₃₆]
                    && c₁₃[clength₉₃₈] == c[clength₉₃₈]))
        && i₁₀ < alength
        && 0 <= i₂
         ==> blength₃ < blength₁₂
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (0 <= i₂
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
          || 0 <= b₁₁[pos]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (0 <= i₂
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
          || c₁₃[pos] < 0));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (0 <= i₂
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
                b₁₁[pos] == a[pos2])));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (0 <= i₂
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
                c₁₃[pos] == a[pos2])));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (0 <= i₂
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
        && pos < alength
        && a[pos] < 0
         ==> i₁₀ < alength
          || (exists pos2: int ::
                b₁₁[pos2] == a[pos])));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (0 <= i₂
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
        && pos < alength
        && a[pos] < 0
         ==> i₁₀ < alength
          || (exists pos2: int ::
                c₁₃[pos2] == a[pos])));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && 0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₃] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₁] == a[i₂]))
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (0 <= i₂
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
        && pos < alength
         ==> i₁₀ < alength
          || (exists pos2: int ::
                b₁₁[pos2] == a[pos])
          || (exists pos2: int ::
                c₁₃[pos2] == a[pos])));

