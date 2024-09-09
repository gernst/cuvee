goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₁₇₂: int, i₁₇₁: int, blength₁₇₀: int ::
              (  0 <= i₁₇₁
                && 0 <= clength₁₇₂
                && clength₁₇₂ < clength₉
                && 0 <= i₁₇₁
                && i₁₇₁ < i₁₀
                && 0 <= blength₁₇₀
                && blength₁₇₀ < blength₁₂
                 ==> a[i₁₇₁] >= 0
                    && i₁₇₁ < alength
                    && 0 <= i₁₇₁
                    && b₁₁[blength₁₇₀] == a[i₁₇₁]
                  ||   (a[i₁₇₁] >= 0
                       ==> false)
                    && i₁₇₁ < alength
                    && 0 <= i₁₇₁
                    && c₁₃[clength₁₇₂] == a[i₁₇₁]))
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

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₂₆₅: int, i₂₆₄: int, blength₂₆₃: int ::
              (  0 <= i₂₆₄
                && 0 <= clength₂₆₅
                && clength₂₆₅ < clength₉
                && 0 <= i₂₆₄
                && i₂₆₄ < i₁₀
                && 0 <= blength₂₆₃
                && blength₂₆₃ < blength₁₂
                 ==> a[i₂₆₄] >= 0
                    && i₂₆₄ < alength
                    && 0 <= i₂₆₄
                    && b₁₁[blength₂₆₃] == a[i₂₆₄]
                  ||   (a[i₂₆₄] >= 0
                       ==> false)
                    && i₂₆₄ < alength
                    && 0 <= i₂₆₄
                    && c₁₃[clength₂₆₅] == a[i₂₆₄]))
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

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₂₉₈: int, i₂₉₇: int, blength₂₉₆: int ::
              (  0 <= i₂₉₇
                && 0 <= clength₂₉₈
                && clength₂₉₈ < clength₉
                && 0 <= i₂₉₇
                && i₂₉₇ < i₁₀
                && 0 <= blength₂₉₆
                && blength₂₉₆ < blength₁₂
                 ==> a[i₂₉₇] >= 0
                    && i₂₉₇ < alength
                    && 0 <= i₂₉₇
                    && b₁₁[blength₂₉₆] == a[i₂₉₇]
                  ||   (a[i₂₉₇] >= 0
                       ==> false)
                    && i₂₉₇ < alength
                    && 0 <= i₂₉₇
                    && c₁₃[clength₂₉₈] == a[i₂₉₇]))
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

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₃₆₂: int, i₃₆₁: int, blength₃₆₀: int ::
              (  0 <= i₃₆₁
                && 0 <= clength₃₆₂
                && clength₃₆₂ < clength₉
                && 0 <= i₃₆₁
                && i₃₆₁ < i₁₀
                && 0 <= blength₃₆₀
                && blength₃₆₀ < blength₁₂
                 ==> a[i₃₆₁] >= 0
                    && i₃₆₁ < alength
                    && 0 <= i₃₆₁
                    && b₁₁[blength₃₆₀] == a[i₃₆₁]
                  ||   (a[i₃₆₁] >= 0
                       ==> false)
                    && i₃₆₁ < alength
                    && 0 <= i₃₆₁
                    && c₁₃[clength₃₆₂] == a[i₃₆₁]))
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

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₅₅: int, i₄₅₄: int, blength₄₅₃: int ::
              (  0 <= i₄₅₄
                && 0 <= clength₄₅₅
                && clength₄₅₅ < clength₉
                && 0 <= i₄₅₄
                && i₄₅₄ < i₁₀
                && 0 <= blength₄₅₃
                && blength₄₅₃ < blength₁₂
                 ==> a[i₄₅₄] >= 0
                    && i₄₅₄ < alength
                    && 0 <= i₄₅₄
                    && b₁₁[blength₄₅₃] == a[i₄₅₄]
                  ||   (a[i₄₅₄] >= 0
                       ==> false)
                    && i₄₅₄ < alength
                    && 0 <= i₄₅₄
                    && c₁₃[clength₄₅₅] == a[i₄₅₄]))
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

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, clength₁: int, i₂: int, blength₃: int ::
      (  0 <= alength
        && 0 <= i₁₀
        && 0 <= clength₉
        && 0 <= i₁₀
        && 0 <= blength₁₂
        && (forall clength₄₈₈: int, i₄₈₇: int, blength₄₈₆: int ::
              (  0 <= i₄₈₇
                && 0 <= clength₄₈₈
                && clength₄₈₈ < clength₉
                && 0 <= i₄₈₇
                && i₄₈₇ < i₁₀
                && 0 <= blength₄₈₆
                && blength₄₈₆ < blength₁₂
                 ==> a[i₄₈₇] >= 0
                    && i₄₈₇ < alength
                    && 0 <= i₄₈₇
                    && b₁₁[blength₄₈₆] == a[i₄₈₇]
                  ||   (a[i₄₈₇] >= 0
                       ==> false)
                    && i₄₈₇ < alength
                    && 0 <= i₄₈₇
                    && c₁₃[clength₄₈₈] == a[i₄₈₇]))
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

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
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
        && 0 <= alength
        && 0 <= pos
        && pos < blength₁₂
         ==> i₁₀ < alength
          || 0 <= b₁₁[pos]));

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
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
        && 0 <= alength
        && 0 <= pos
        && pos < clength₉
         ==> i₁₀ < alength
          || c₁₃[pos] < 0));

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
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
        && 0 <= alength
        && 0 <= pos
        && pos < blength₁₂
         ==> i₁₀ < alength
          || (exists pos2: int ::
                b₁₁[pos] == a[pos2])));

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
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
        && 0 <= alength
        && 0 <= pos
        && pos < clength₉
         ==> i₁₀ < alength
          || (exists pos2: int ::
                c₁₃[pos] == a[pos2])));

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
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
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a[pos] < 0
         ==> i₁₀ < alength
          || (exists pos2: int ::
                b₁₁[pos2] == a[pos])));

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
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
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a[pos] < 0
         ==> i₁₀ < alength
          || (exists pos2: int ::
                c₁₃[pos2] == a[pos])));

goal (forall a: [int]int, alength: int, clength₉: int, i₁₀: int, b₁₁: [int]int, blength₁₂: int, c₁₃: [int]int, pos: int ::
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
        && 0 <= alength
        && 0 <= pos
        && pos < alength
         ==> i₁₀ < alength
          || (exists pos2: int ::
                b₁₁[pos2] == a[pos])
          || (exists pos2: int ::
                c₁₃[pos2] == a[pos])));

