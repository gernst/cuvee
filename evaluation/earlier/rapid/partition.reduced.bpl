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
        && (forall clength₅₀₃: int, i₅₀₂: int, blength₅₀₁: int ::
              (  clength₅₀₃ + clength₅₀₃ == i₅₀₂ + i₅₀₂
                && clength₅₀₃ + clength₅₀₃ == blength₅₀₁ + blength₅₀₁
                && 0 <= clength₅₀₃
                && clength₅₀₃ < clength₉
                && 0 <= i₅₀₂
                && i₅₀₂ < i₁₀
                && 0 <= blength₅₀₁
                && blength₅₀₁ < blength₁₂
                 ==> a[i₅₀₂] >= 0
                    && i₅₀₂ < alength
                    && b₁₁[blength₅₀₁] == a[i₅₀₂]
                  ||   (a[i₅₀₂] >= 0
                       ==> false)
                    && i₅₀₂ < alength
                    && c₁₃[clength₅₀₃] == a[i₅₀₂]))
        && (forall clength₅₀₆: int, i₅₀₅: int, blength₅₀₄: int ::
              (  clength₅₀₆ + clength₅₀₆ == i₅₀₅ + i₅₀₅
                && clength₅₀₆ + clength₅₀₆ == blength₅₀₄ + blength₅₀₄
                 ==> 0 <= clength₅₀₆
                    && clength₅₀₆ < clength₉
                    && 0 <= i₅₀₅
                    && i₅₀₅ < i₁₀
                    && 0 <= blength₅₀₄
                    && blength₅₀₄ < blength₁₂
                  ||   b₁₁[blength₅₀₄] == b[blength₅₀₄]
                    && c₁₃[clength₅₀₆] == c[clength₅₀₆]))
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

