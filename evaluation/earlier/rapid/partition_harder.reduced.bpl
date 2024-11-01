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
        && (forall clength₄₆₁: int, i₄₆₀: int, blength₄₅₉: int ::
              (  clength₄₆₁ + clength₄₆₁ == i₄₆₀ + i₄₆₀
                && clength₄₆₁ + clength₄₆₁ == blength₄₅₉ + blength₄₅₉
                && 0 <= clength₄₆₁
                && clength₄₆₁ < clength₉
                && 0 <= i₄₆₀
                && i₄₆₀ < i₁₀
                && 0 <= blength₄₅₉
                && blength₄₅₉ < blength₁₂
                 ==> a[i₄₆₀] >= 0
                    && i₄₆₀ < alength
                    && b₁₁[blength₄₅₉] == a[i₄₆₀]
                  ||   (a[i₄₆₀] >= 0
                       ==> false)
                    && i₄₆₀ < alength
                    && c₁₃[clength₄₆₁] == a[i₄₆₀]))
        && (forall clength₄₆₄: int, i₄₆₃: int, blength₄₆₂: int ::
              (  clength₄₆₄ + clength₄₆₄ == i₄₆₃ + i₄₆₃
                && clength₄₆₄ + clength₄₆₄ == blength₄₆₂ + blength₄₆₂
                 ==> 0 <= clength₄₆₄
                    && clength₄₆₄ < clength₉
                    && 0 <= i₄₆₃
                    && i₄₆₃ < i₁₀
                    && 0 <= blength₄₆₂
                    && blength₄₆₂ < blength₁₂
                  ||   b₁₁[blength₄₆₂] == b[blength₄₆₂]
                    && c₁₃[clength₄₆₄] == c[clength₄₆₄]))
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

