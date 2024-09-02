goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₇: [int]int, blength₈: int, i₉: int, pos: int ::
      (  0 <= alength
        && 0 <= i₉
        && 0 <= blength₈
        && 0 <= i₉
        && i₉ <= alength
        && (forall x₃: int, blength₁: int ::
              (  x₃ == blength₁
                && 0 <= blength₁
                && blength₁ < blength₈
                 ==> (exists blength₁: int, i₂: int ::
                        a1[i₂] == a2[i₂]
                        && i₂ < alength
                        && 0 <= i₂
                        && x₃ == blength₁
                        && 0 <= blength₁
                        && blength₁ < blength₈
                        && 0 <= i₂
                        && i₂ < i₉
                        && b₇[x₃] == i₂)))
        && (forall x₃: int ::
                (exists blength₁: int ::
                        x₃ == blength₁
                        && 0 <= blength₁
                        && blength₁ < blength₈)
                || b₇[x₃] == b[x₃])
        && (forall blength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= blength₁
                && blength₁ < blength₈
                && 0 <= i₂
                && i₂ < i₉
                 ==> i₂ < alength))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a1[pos] == a2[pos]
         ==> i₉ < alength
          || (exists pos2: int ::
                b₇[pos2] == pos)));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₇: [int]int, blength₈: int, i₉: int, pos: int ::
      (  0 <= alength
        && 0 <= i₉
        && 0 <= blength₈
        && 0 <= i₉
        && i₉ <= alength
        && (forall x₃: int, blength₁: int ::
              (  x₃ == blength₁
                && 0 <= blength₁
                && blength₁ < blength₈
                 ==> (exists blength₁: int, i₂: int ::
                        a1[i₂] == a2[i₂]
                        && i₂ < alength
                        && 0 <= i₂
                        && x₃ == blength₁
                        && 0 <= blength₁
                        && blength₁ < blength₈
                        && 0 <= i₂
                        && i₂ < i₉
                        && b₇[x₃] == i₂)))
        && (forall x₃: int ::
                (exists blength₁: int ::
                        x₃ == blength₁
                        && 0 <= blength₁
                        && blength₁ < blength₈)
                || b₇[x₃] == b[x₃])
        && (forall blength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= blength₁
                && blength₁ < blength₈
                && 0 <= i₂
                && i₂ < i₉
                 ==> i₂ < alength))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a1[pos] == a2[pos]
         ==> i₉ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < blength₈
                  && b₇[pos2] == pos)));

