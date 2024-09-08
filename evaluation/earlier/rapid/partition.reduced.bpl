goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₂₄₀: int, i₂₃₉: int, blength₂₃₈: int ::
              (  0 <= clength₂₄₀
                && clength₂₄₀ < clength₉
                && 0 <= i₂₃₉
                && i₂₃₉ < i₁₀
                && 0 <= blength₂₃₈
                && blength₂₃₈ < blength₁₂
                 ==> a[i₂₃₉] >= 0
                    && i₂₃₉ < alength
                    && 0 <= i₂₃₉
                    && b₁₁[blength₂₃₈] == a[i₂₃₉]
                  ||   (a[i₂₃₉] >= 0
                       ==> false)
                    && i₂₃₉ < alength
                    && 0 <= i₂₃₉
                    && c₁₃[clength₂₄₀] == a[i₂₃₉]))
        && (forall clength₂₄₃: int, i₂₄₂: int, blength₂₄₁: int ::
                  0 <= clength₂₄₃
                  && clength₂₄₃ < clength₉
                  && 0 <= i₂₄₂
                  && i₂₄₂ < i₁₀
                  && 0 <= blength₂₄₁
                  && blength₂₄₁ < blength₁₂
                ||   b₁₁[blength₂₄₁] == b[blength₂₄₁]
                  && c₁₃[clength₂₄₃] == c[clength₂₄₃])
        && i₁₀ < alength
        && a[i₁₀] >= 0
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
        && i₁₀ <= alength
        && (forall clength₃₅₄: int, i₃₅₃: int, blength₃₅₂: int ::
              (  0 <= clength₃₅₄
                && clength₃₅₄ < clength₉
                && 0 <= i₃₅₃
                && i₃₅₃ < i₁₀
                && 0 <= blength₃₅₂
                && blength₃₅₂ < blength₁₂
                 ==> a[i₃₅₃] >= 0
                    && i₃₅₃ < alength
                    && 0 <= i₃₅₃
                    && b₁₁[blength₃₅₂] == a[i₃₅₃]
                  ||   (a[i₃₅₃] >= 0
                       ==> false)
                    && i₃₅₃ < alength
                    && 0 <= i₃₅₃
                    && c₁₃[clength₃₅₄] == a[i₃₅₃]))
        && (forall clength₃₅₇: int, i₃₅₆: int, blength₃₅₅: int ::
                  0 <= clength₃₅₇
                  && clength₃₅₇ < clength₉
                  && 0 <= i₃₅₆
                  && i₃₅₆ < i₁₀
                  && 0 <= blength₃₅₅
                  && blength₃₅₅ < blength₁₂
                ||   b₁₁[blength₃₅₅] == b[blength₃₅₅]
                  && c₁₃[clength₃₅₇] == c[clength₃₅₇])
        && i₁₀ < alength
        && a[i₁₀] >= 0
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
        && i₁₀ <= alength
        && (forall clength₃₉₆: int, i₃₉₅: int, blength₃₉₄: int ::
              (  0 <= clength₃₉₆
                && clength₃₉₆ < clength₉
                && 0 <= i₃₉₅
                && i₃₉₅ < i₁₀
                && 0 <= blength₃₉₄
                && blength₃₉₄ < blength₁₂
                 ==> a[i₃₉₅] >= 0
                    && i₃₉₅ < alength
                    && 0 <= i₃₉₅
                    && b₁₁[blength₃₉₄] == a[i₃₉₅]
                  ||   (a[i₃₉₅] >= 0
                       ==> false)
                    && i₃₉₅ < alength
                    && 0 <= i₃₉₅
                    && c₁₃[clength₃₉₆] == a[i₃₉₅]))
        && (forall clength₃₉₉: int, i₃₉₈: int, blength₃₉₇: int ::
                  0 <= clength₃₉₉
                  && clength₃₉₉ < clength₉
                  && 0 <= i₃₉₈
                  && i₃₉₈ < i₁₀
                  && 0 <= blength₃₉₇
                  && blength₃₉₇ < blength₁₂
                ||   b₁₁[blength₃₉₇] == b[blength₃₉₇]
                  && c₁₃[clength₃₉₉] == c[clength₃₉₉])
        && i₁₀ < alength
        && a[i₁₀] >= 0
        && 0 <= clength₁
        && clength₁ < clength₉
        && 0 <= i₂
        && i₂ < i₁₀ + 1
        && 0 <= blength₃
        && blength₃ < blength₁₂ + 1
         ==> b₁₁[blength₁₂ := a[i₁₀]][blength₃] == a[i₂]
          || c₁₃[clength₁] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₄₁₂: int, i₂: int, blength₄₁₁: int ::
              (  0 <= clength₄₁₂
                && clength₄₁₂ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₄₁₁
                && blength₄₁₁ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₄₁₁] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₄₁₂] == a[i₂]))
        && (forall clength₄₁₄: int, i₂: int, blength₄₁₃: int ::
                  0 <= clength₄₁₄
                  && clength₄₁₄ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₄₁₃
                  && blength₄₁₃ < blength₁₂
                ||   b₁₁[blength₄₁₃] == b[blength₄₁₃]
                  && c₁₃[clength₄₁₄] == c[clength₄₁₄])
        && i₁₀ < alength
        && a[i₁₀] >= 0
         ==> 0 <= clength₁
          || b₁₁[blength₁₂ := a[i₁₀]][blength₃] == b[blength₃]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₄₃₇: int, i₂: int, blength₄₃₆: int ::
              (  0 <= clength₄₃₇
                && clength₄₃₇ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₄₃₆
                && blength₄₃₆ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₄₃₆] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₄₃₇] == a[i₂]))
        && (forall clength₄₃₉: int, i₂: int, blength₄₃₈: int ::
                  0 <= clength₄₃₉
                  && clength₄₃₉ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₄₃₈
                  && blength₄₃₈ < blength₁₂
                ||   b₁₁[blength₄₃₈] == b[blength₄₃₈]
                  && c₁₃[clength₄₃₉] == c[clength₄₃₉])
        && i₁₀ < alength
        && a[i₁₀] >= 0
         ==> clength₁ < clength₉
          || b₁₁[blength₁₂ := a[i₁₀]][blength₃] == b[blength₃]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₁: int, i₄₆₂: int, blength₄₆₁: int ::
              (  0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₄₆₂
                && i₄₆₂ < i₁₀
                && 0 <= blength₄₆₁
                && blength₄₆₁ < blength₁₂
                 ==> a[i₄₆₂] >= 0
                    && i₄₆₂ < alength
                    && 0 <= i₄₆₂
                    && b₁₁[blength₄₆₁] == a[i₄₆₂]
                  ||   (a[i₄₆₂] >= 0
                       ==> false)
                    && i₄₆₂ < alength
                    && 0 <= i₄₆₂
                    && c₁₃[clength₁] == a[i₄₆₂]))
        && (forall clength₁: int, i₄₆₄: int, blength₄₆₃: int ::
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₄₆₄
                  && i₄₆₄ < i₁₀
                  && 0 <= blength₄₆₃
                  && blength₄₆₃ < blength₁₂
                ||   b₁₁[blength₄₆₃] == b[blength₄₆₃]
                  && c₁₃[clength₁] == c[clength₁])
        && i₁₀ < alength
        && a[i₁₀] >= 0
         ==> 0 <= i₂
          || b₁₁[blength₁₂ := a[i₁₀]][blength₃] == b[blength₃]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₁: int, i₄₈₈: int, blength₄₈₇: int ::
              (  0 <= clength₁
                && clength₁ < clength₉
                && 0 <= i₄₈₈
                && i₄₈₈ < i₁₀
                && 0 <= blength₄₈₇
                && blength₄₈₇ < blength₁₂
                 ==> a[i₄₈₈] >= 0
                    && i₄₈₈ < alength
                    && 0 <= i₄₈₈
                    && b₁₁[blength₄₈₇] == a[i₄₈₈]
                  ||   (a[i₄₈₈] >= 0
                       ==> false)
                    && i₄₈₈ < alength
                    && 0 <= i₄₈₈
                    && c₁₃[clength₁] == a[i₄₈₈]))
        && (forall clength₁: int, i₄₉₀: int, blength₄₈₉: int ::
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₄₉₀
                  && i₄₉₀ < i₁₀
                  && 0 <= blength₄₈₉
                  && blength₄₈₉ < blength₁₂
                ||   b₁₁[blength₄₈₉] == b[blength₄₈₉]
                  && c₁₃[clength₁] == c[clength₁])
        && i₁₀ < alength
        && a[i₁₀] >= 0
         ==> i₂ < i₁₀ + 1
          || b₁₁[blength₁₂ := a[i₁₀]][blength₃] == b[blength₃]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₆₃₀: int, i₆₂₉: int, blength₆₂₈: int ::
              (  0 <= clength₆₃₀
                && clength₆₃₀ < clength₉
                && 0 <= i₆₂₉
                && i₆₂₉ < i₁₀
                && 0 <= blength₆₂₈
                && blength₆₂₈ < blength₁₂
                 ==> a[i₆₂₉] >= 0
                    && i₆₂₉ < alength
                    && 0 <= i₆₂₉
                    && b₁₁[blength₆₂₈] == a[i₆₂₉]
                  ||   (a[i₆₂₉] >= 0
                       ==> false)
                    && i₆₂₉ < alength
                    && 0 <= i₆₂₉
                    && c₁₃[clength₆₃₀] == a[i₆₂₉]))
        && (forall clength₆₃₃: int, i₆₃₂: int, blength₆₃₁: int ::
                  0 <= clength₆₃₃
                  && clength₆₃₃ < clength₉
                  && 0 <= i₆₃₂
                  && i₆₃₂ < i₁₀
                  && 0 <= blength₆₃₁
                  && blength₆₃₁ < blength₁₂
                ||   b₁₁[blength₆₃₁] == b[blength₆₃₁]
                  && c₁₃[clength₆₃₃] == c[clength₆₃₃])
        && i₁₀ < alength
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
        && i₁₀ <= alength
        && (forall clength₇₄₄: int, i₇₄₃: int, blength₇₄₂: int ::
              (  0 <= clength₇₄₄
                && clength₇₄₄ < clength₉
                && 0 <= i₇₄₃
                && i₇₄₃ < i₁₀
                && 0 <= blength₇₄₂
                && blength₇₄₂ < blength₁₂
                 ==> a[i₇₄₃] >= 0
                    && i₇₄₃ < alength
                    && 0 <= i₇₄₃
                    && b₁₁[blength₇₄₂] == a[i₇₄₃]
                  ||   (a[i₇₄₃] >= 0
                       ==> false)
                    && i₇₄₃ < alength
                    && 0 <= i₇₄₃
                    && c₁₃[clength₇₄₄] == a[i₇₄₃]))
        && (forall clength₇₄₇: int, i₇₄₆: int, blength₇₄₅: int ::
                  0 <= clength₇₄₇
                  && clength₇₄₇ < clength₉
                  && 0 <= i₇₄₆
                  && i₇₄₆ < i₁₀
                  && 0 <= blength₇₄₅
                  && blength₇₄₅ < blength₁₂
                ||   b₁₁[blength₇₄₅] == b[blength₇₄₅]
                  && c₁₃[clength₇₄₇] == c[clength₇₄₇])
        && i₁₀ < alength
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
        && i₁₀ <= alength
        && (forall clength₇₈₆: int, i₇₈₅: int, blength₇₈₄: int ::
              (  0 <= clength₇₈₆
                && clength₇₈₆ < clength₉
                && 0 <= i₇₈₅
                && i₇₈₅ < i₁₀
                && 0 <= blength₇₈₄
                && blength₇₈₄ < blength₁₂
                 ==> a[i₇₈₅] >= 0
                    && i₇₈₅ < alength
                    && 0 <= i₇₈₅
                    && b₁₁[blength₇₈₄] == a[i₇₈₅]
                  ||   (a[i₇₈₅] >= 0
                       ==> false)
                    && i₇₈₅ < alength
                    && 0 <= i₇₈₅
                    && c₁₃[clength₇₈₆] == a[i₇₈₅]))
        && (forall clength₇₈₉: int, i₇₈₈: int, blength₇₈₇: int ::
                  0 <= clength₇₈₉
                  && clength₇₈₉ < clength₉
                  && 0 <= i₇₈₈
                  && i₇₈₈ < i₁₀
                  && 0 <= blength₇₈₇
                  && blength₇₈₇ < blength₁₂
                ||   b₁₁[blength₇₈₇] == b[blength₇₈₇]
                  && c₁₃[clength₇₈₉] == c[clength₇₈₉])
        && i₁₀ < alength
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
        && i₁₀ <= alength
        && (forall clength₈₅₅: int, i₈₅₄: int, blength₃: int ::
              (  0 <= clength₈₅₅
                && clength₈₅₅ < clength₉
                && 0 <= i₈₅₄
                && i₈₅₄ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₈₅₄] >= 0
                    && i₈₅₄ < alength
                    && 0 <= i₈₅₄
                    && b₁₁[blength₃] == a[i₈₅₄]
                  ||   (a[i₈₅₄] >= 0
                       ==> false)
                    && i₈₅₄ < alength
                    && 0 <= i₈₅₄
                    && c₁₃[clength₈₅₅] == a[i₈₅₄]))
        && (forall clength₈₅₇: int, i₈₅₆: int, blength₃: int ::
                  0 <= clength₈₅₇
                  && clength₈₅₇ < clength₉
                  && 0 <= i₈₅₆
                  && i₈₅₆ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₈₅₇] == c[clength₈₅₇])
        && i₁₀ < alength
         ==> 0 <= i₂
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₈₈₁: int, i₈₈₀: int, blength₃: int ::
              (  0 <= clength₈₈₁
                && clength₈₈₁ < clength₉
                && 0 <= i₈₈₀
                && i₈₈₀ < i₁₀
                && 0 <= blength₃
                && blength₃ < blength₁₂
                 ==> a[i₈₈₀] >= 0
                    && i₈₈₀ < alength
                    && 0 <= i₈₈₀
                    && b₁₁[blength₃] == a[i₈₈₀]
                  ||   (a[i₈₈₀] >= 0
                       ==> false)
                    && i₈₈₀ < alength
                    && 0 <= i₈₈₀
                    && c₁₃[clength₈₈₁] == a[i₈₈₀]))
        && (forall clength₈₈₃: int, i₈₈₂: int, blength₃: int ::
                  0 <= clength₈₈₃
                  && clength₈₈₃ < clength₉
                  && 0 <= i₈₈₂
                  && i₈₈₂ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₈₈₃] == c[clength₈₈₃])
        && i₁₀ < alength
         ==> i₂ < i₁₀ + 1
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₉₀₆: int, i₂: int, blength₉₀₅: int ::
              (  0 <= clength₉₀₆
                && clength₉₀₆ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₉₀₅
                && blength₉₀₅ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₉₀₅] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₉₀₆] == a[i₂]))
        && (forall clength₉₀₈: int, i₂: int, blength₉₀₇: int ::
                  0 <= clength₉₀₈
                  && clength₉₀₈ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₉₀₇
                  && blength₉₀₇ < blength₁₂
                ||   b₁₁[blength₉₀₇] == b[blength₉₀₇]
                  && c₁₃[clength₉₀₈] == c[clength₉₀₈])
        && i₁₀ < alength
         ==> 0 <= blength₃
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₉₃₁: int, i₂: int, blength₉₃₀: int ::
              (  0 <= clength₉₃₁
                && clength₉₃₁ < clength₉
                && 0 <= i₂
                && i₂ < i₁₀
                && 0 <= blength₉₃₀
                && blength₉₃₀ < blength₁₂
                 ==> a[i₂] >= 0
                    && i₂ < alength
                    && 0 <= i₂
                    && b₁₁[blength₉₃₀] == a[i₂]
                  ||   (a[i₂] >= 0
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂
                    && c₁₃[clength₉₃₁] == a[i₂]))
        && (forall clength₉₃₃: int, i₂: int, blength₉₃₂: int ::
                  0 <= clength₉₃₃
                  && clength₉₃₃ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₉₃₂
                  && blength₉₃₂ < blength₁₂
                ||   b₁₁[blength₉₃₂] == b[blength₉₃₂]
                  && c₁₃[clength₉₃₃] == c[clength₉₃₃])
        && i₁₀ < alength
         ==> blength₃ < blength₁₂
          || a[i₁₀] >= 0
          || c₁₃[clength₉ := a[i₁₀]][clength₁] == c[clength₁]));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && i₁₀ <= alength
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= clength₁
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
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₁] == c[clength₁])
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
        && i₁₀ <= alength
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= clength₁
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
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₁] == c[clength₁])
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
        && i₁₀ <= alength
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= clength₁
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
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₁] == c[clength₁])
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
        && i₁₀ <= alength
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= clength₁
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
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₁] == c[clength₁])
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
        && i₁₀ <= alength
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= clength₁
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
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₁] == c[clength₁])
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
        && i₁₀ <= alength
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= clength₁
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
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₁] == c[clength₁])
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
        && i₁₀ <= alength
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= clength₁
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
                  0 <= clength₁
                  && clength₁ < clength₉
                  && 0 <= i₂
                  && i₂ < i₁₀
                  && 0 <= blength₃
                  && blength₃ < blength₁₂
                ||   b₁₁[blength₃] == b[blength₃]
                  && c₁₃[clength₁] == c[clength₁])
        && 0 <= alength
        && 0 <= pos
        && pos < alength
         ==> i₁₀ < alength
          || (exists pos2: int ::
                b₁₁[pos2] == a[pos])
          || (exists pos2: int ::
                c₁₃[pos2] == a[pos])));

