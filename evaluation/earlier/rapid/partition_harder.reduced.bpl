goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₁₁: int, i₁₂: int, b₁₃: [int]int, blength₁₄: int, c₁₅: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₂
        && 0 <= clength₁₁
        && 0 <= i₁₂
        && 0 <= blength₁₄
        && i₁₂ <= alength
        && (forall x₄: int, blength₃: int ::
              (  x₄ == blength₃
                && 0 <= blength₃
                && blength₃ < blength₁₄
                 ==> (exists i₂: int, blength₃: int ::
                        a[i₂] >= 0
                        && i₂ < alength
                        && 0 <= i₂
                        && x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < blength₁₄
                        && b₁₃[x₄] == a[i₂])))
        && (forall x₄: int ::
                (exists blength₃: int ::
                        x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < blength₁₄)
                || b₁₃[x₄] == b[x₄])
        && (forall x₅: int, clength₁: int ::
              (  x₅ == clength₁
                && 0 <= clength₁
                && clength₁ < clength₁₁
                 ==> (exists i₂: int ::
                      (a[i₂] >= 0
                         ==> false))))
        && (forall x₅: int ::
                (exists clength₁: int ::
                        x₅ == clength₁
                        && 0 <= clength₁
                        && clength₁ < clength₁₁)
                || c₁₅[x₅] == c[x₅])
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && clength₁ <= clength₁
                && i₂ <= i₂
                && blength₃ <= blength₃
                && 0 <= clength₁
                && clength₁ < clength₁₁
                && 0 <= i₂
                && i₂ < i₁₂
                && 0 <= blength₃
                && blength₃ < blength₁₄
                 ==> i₂ < alength))
        && 0 <= alength
        && 0 <= pos
        && pos < clength₁₁
         ==> i₁₂ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < alength
                  && c₁₅[pos] == a[pos2])));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₁₁: int, i₁₂: int, b₁₃: [int]int, blength₁₄: int, c₁₅: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₂
        && 0 <= clength₁₁
        && 0 <= i₁₂
        && 0 <= blength₁₄
        && i₁₂ <= alength
        && (forall x₄: int, blength₃: int ::
              (  x₄ == blength₃
                && 0 <= blength₃
                && blength₃ < blength₁₄
                 ==> (exists i₂: int, blength₃: int ::
                        a[i₂] >= 0
                        && i₂ < alength
                        && 0 <= i₂
                        && x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < blength₁₄
                        && b₁₃[x₄] == a[i₂])))
        && (forall x₄: int ::
                (exists blength₃: int ::
                        x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < blength₁₄)
                || b₁₃[x₄] == b[x₄])
        && (forall x₅: int, clength₁: int ::
              (  x₅ == clength₁
                && 0 <= clength₁
                && clength₁ < clength₁₁
                 ==> (exists i₂: int ::
                      (a[i₂] >= 0
                         ==> false))))
        && (forall x₅: int ::
                (exists clength₁: int ::
                        x₅ == clength₁
                        && 0 <= clength₁
                        && clength₁ < clength₁₁)
                || c₁₅[x₅] == c[x₅])
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && clength₁ <= clength₁
                && i₂ <= i₂
                && blength₃ <= blength₃
                && 0 <= clength₁
                && clength₁ < clength₁₁
                && 0 <= i₂
                && i₂ < i₁₂
                && 0 <= blength₃
                && blength₃ < blength₁₄
                 ==> i₂ < alength))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && 0 <= a[pos]
         ==> i₁₂ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < blength₁₄
                  && b₁₃[pos2] == a[pos])));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₁₁: int, i₁₂: int, b₁₃: [int]int, blength₁₄: int, c₁₅: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₂
        && 0 <= clength₁₁
        && 0 <= i₁₂
        && 0 <= blength₁₄
        && i₁₂ <= alength
        && (forall x₄: int, blength₃: int ::
              (  x₄ == blength₃
                && 0 <= blength₃
                && blength₃ < blength₁₄
                 ==> (exists i₂: int, blength₃: int ::
                        a[i₂] >= 0
                        && i₂ < alength
                        && 0 <= i₂
                        && x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < blength₁₄
                        && b₁₃[x₄] == a[i₂])))
        && (forall x₄: int ::
                (exists blength₃: int ::
                        x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < blength₁₄)
                || b₁₃[x₄] == b[x₄])
        && (forall x₅: int, clength₁: int ::
              (  x₅ == clength₁
                && 0 <= clength₁
                && clength₁ < clength₁₁
                 ==> (exists i₂: int ::
                      (a[i₂] >= 0
                         ==> false))))
        && (forall x₅: int ::
                (exists clength₁: int ::
                        x₅ == clength₁
                        && 0 <= clength₁
                        && clength₁ < clength₁₁)
                || c₁₅[x₅] == c[x₅])
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && clength₁ <= clength₁
                && i₂ <= i₂
                && blength₃ <= blength₃
                && 0 <= clength₁
                && clength₁ < clength₁₁
                && 0 <= i₂
                && i₂ < i₁₂
                && 0 <= blength₃
                && blength₃ < blength₁₄
                 ==> i₂ < alength))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && 0 < a[pos]
         ==> i₁₂ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < clength₁₁
                  && c₁₅[pos2] == a[pos])));

goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int, clength₁₁: int, i₁₂: int, b₁₃: [int]int, blength₁₄: int, c₁₅: [int]int, pos: int ::
      (  0 <= alength
        && 0 <= i₁₂
        && 0 <= clength₁₁
        && 0 <= i₁₂
        && 0 <= blength₁₄
        && i₁₂ <= alength
        && (forall x₄: int, blength₃: int ::
              (  x₄ == blength₃
                && 0 <= blength₃
                && blength₃ < blength₁₄
                 ==> (exists i₂: int, blength₃: int ::
                        a[i₂] >= 0
                        && i₂ < alength
                        && 0 <= i₂
                        && x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < blength₁₄
                        && b₁₃[x₄] == a[i₂])))
        && (forall x₄: int ::
                (exists blength₃: int ::
                        x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < blength₁₄)
                || b₁₃[x₄] == b[x₄])
        && (forall x₅: int, clength₁: int ::
              (  x₅ == clength₁
                && 0 <= clength₁
                && clength₁ < clength₁₁
                 ==> (exists i₂: int ::
                      (a[i₂] >= 0
                         ==> false))))
        && (forall x₅: int ::
                (exists clength₁: int ::
                        x₅ == clength₁
                        && 0 <= clength₁
                        && clength₁ < clength₁₁)
                || c₁₅[x₅] == c[x₅])
        && (forall clength₁: int, i₂: int, blength₃: int ::
              (  0 <= i₂
                && clength₁ <= clength₁
                && i₂ <= i₂
                && blength₃ <= blength₃
                && 0 <= clength₁
                && clength₁ < clength₁₁
                && 0 <= i₂
                && i₂ < i₁₂
                && 0 <= blength₃
                && blength₃ < blength₁₄
                 ==> i₂ < alength))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
         ==> i₁₂ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < blength₁₄
                  && b₁₃[pos2] == a[pos])
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < clength₁₁
                  && c₁₅[pos2] == a[pos])));

