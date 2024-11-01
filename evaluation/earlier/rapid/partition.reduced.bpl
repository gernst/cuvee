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
        && (forall clength₃₅₉: int, i₃₅₈: int, blength₃₅₇: int ::
              (  clength₃₅₉ + clength₃₅₉ == i₃₅₈ + i₃₅₈
                && clength₃₅₉ + clength₃₅₉ == blength₃₅₇ + blength₃₅₇
                && 0 <= clength₃₅₉
                && clength₃₅₉ < clength₉
                && 0 <= i₃₅₈
                && i₃₅₈ < i₁₀
                && 0 <= blength₃₅₇
                && blength₃₅₇ < blength₁₂
                 ==> a[i₃₅₈] >= 0
                    && i₃₅₈ < alength
                    && b₁₁[blength₃₅₇] == a[i₃₅₈]
                  ||   (a[i₃₅₈] >= 0
                       ==> false)
                    && i₃₅₈ < alength
                    && c₁₃[clength₃₅₉] == a[i₃₅₈]))
        && (forall clength₃₆₂: int, i₃₆₁: int, blength₃₆₀: int ::
              (  clength₃₆₂ + clength₃₆₂ == i₃₆₁ + i₃₆₁
                && clength₃₆₂ + clength₃₆₂ == blength₃₆₀ + blength₃₆₀
                 ==> 0 <= clength₃₆₂
                    && clength₃₆₂ < clength₉
                    && 0 <= i₃₆₁
                    && i₃₆₁ < i₁₀
                    && 0 <= blength₃₆₀
                    && blength₃₆₀ < blength₁₂
                  ||   b₁₁[blength₃₆₀] == b[blength₃₆₀]
                    && c₁₃[clength₃₆₂] == c[clength₃₆₂]))
        && i₁₀ < alength
        && clength₁ + clength₁ == i₂ + i₂
        && clength₁ + clength₁ == blength₃ + blength₃
        && 0 <= clength₁
        && clength₁ < clength₉ + 1
        && 0 <= i₂
        && i₂ < i₁₀ + 1
        && 0 <= blength₃
        && blength₃ < blength₁₂
         ==> a[i₁₀] >= 0
          ||   a[i₂] >= 0
            && i₂ < alength
            && b₁₁[blength₃] == a[i₂]
          ||   (a[i₂] >= 0
               ==> false)
            && i₂ < alength
            && c₁₃[clength₉ := a[i₁₀]][clength₁] == a[i₂]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && clength₉ + 0 == i₁₀ + 0
        && clength₉ + 0 == 0 + blength₁₂
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₁₃: int, i₄₁₂: int, blength₄₁₁: int ::
              (  clength₄₁₃ + clength₄₁₃ == i₄₁₂ + i₄₁₂
                && clength₄₁₃ + clength₄₁₃ == blength₄₁₁ + blength₄₁₁
                && 0 <= clength₄₁₃
                && clength₄₁₃ < clength₉
                && 0 <= i₄₁₂
                && i₄₁₂ < i₁₀
                && 0 <= blength₄₁₁
                && blength₄₁₁ < blength₁₂
                 ==> a[i₄₁₂] >= 0
                    && i₄₁₂ < alength
                    && b₁₁[blength₄₁₁] == a[i₄₁₂]
                  ||   (a[i₄₁₂] >= 0
                       ==> false)
                    && i₄₁₂ < alength
                    && c₁₃[clength₄₁₃] == a[i₄₁₂]))
        && (forall clength₄₁₆: int, i₄₁₅: int, blength₄₁₄: int ::
              (  clength₄₁₆ + clength₄₁₆ == i₄₁₅ + i₄₁₅
                && clength₄₁₆ + clength₄₁₆ == blength₄₁₄ + blength₄₁₄
                 ==> 0 <= clength₄₁₆
                    && clength₄₁₆ < clength₉
                    && 0 <= i₄₁₅
                    && i₄₁₅ < i₁₀
                    && 0 <= blength₄₁₄
                    && blength₄₁₄ < blength₁₂
                  ||   b₁₁[blength₄₁₄] == b[blength₄₁₄]
                    && c₁₃[clength₄₁₆] == c[clength₄₁₆]))
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
        && (forall clength₅₁₅: int, i₅₁₄: int, blength₅₁₃: int ::
              (  clength₅₁₅ + clength₅₁₅ == i₅₁₄ + i₅₁₄
                && clength₅₁₅ + clength₅₁₅ == blength₅₁₃ + blength₅₁₃
                && 0 <= clength₅₁₅
                && clength₅₁₅ < clength₉
                && 0 <= i₅₁₄
                && i₅₁₄ < i₁₀
                && 0 <= blength₅₁₃
                && blength₅₁₃ < blength₁₂
                 ==> a[i₅₁₄] >= 0
                    && i₅₁₄ < alength
                    && b₁₁[blength₅₁₃] == a[i₅₁₄]
                  ||   (a[i₅₁₄] >= 0
                       ==> false)
                    && i₅₁₄ < alength
                    && c₁₃[clength₅₁₅] == a[i₅₁₄]))
        && (forall clength₅₁₈: int, i₅₁₇: int, blength₅₁₆: int ::
              (  clength₅₁₈ + clength₅₁₈ == i₅₁₇ + i₅₁₇
                && clength₅₁₈ + clength₅₁₈ == blength₅₁₆ + blength₅₁₆
                 ==> 0 <= clength₅₁₈
                    && clength₅₁₈ < clength₉
                    && 0 <= i₅₁₇
                    && i₅₁₇ < i₁₀
                    && 0 <= blength₅₁₆
                    && blength₅₁₆ < blength₁₂
                  ||   b₁₁[blength₅₁₆] == b[blength₅₁₆]
                    && c₁₃[clength₅₁₈] == c[clength₅₁₈]))
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
          || 0 <= b₁₁[pos]));

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
          || c₁₃[pos] < 0));

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
                b₁₁[pos] == a[pos2])));

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
                c₁₃[pos] == a[pos2])));

