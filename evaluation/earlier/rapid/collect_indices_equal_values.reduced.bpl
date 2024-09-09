goal (forall a1: [int]int, a2: [int]int, alength: int, b₆: [int]int, blength₇: int, i₈: int, blength₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁₆₀: int, i₁₅₉: int ::
              (  0 <= i₁₅₉
                && 0 <= blength₁₆₀
                && blength₁₆₀ < blength₇
                && 0 <= i₁₅₉
                && i₁₅₉ < i₈
                 ==> a1[i₁₅₉] == a2[i₁₅₉]
                    && i₁₅₉ < alength
                    && 0 <= i₁₅₉
                    && b₆[blength₁₆₀] == i₁₅₉
                  ||   (a1[i₁₅₉] == a2[i₁₅₉]
                       ==> false)
                    && i₁₅₉ < alength
                    && 0 <= i₁₅₉))
        && i₈ < alength
        && a1[i₈] == a2[i₈]
        && 0 <= i₂
        && 0 <= blength₁
        && blength₁ < blength₇ + 1
        && 0 <= i₂
        && i₂ < i₈ + 1
        && a1[i₂] == a2[i₂]
         ==> b₆[blength₇ := i₈][blength₁] == i₂));

goal (forall a1: [int]int, a2: [int]int, alength: int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && 0 <= i₂
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂))
        && 0 <= alength
        && 0 <= pos
        && pos < blength₇
         ==> i₈ < alength
          || 0 <= b₆[pos]));

goal (forall a1: [int]int, a2: [int]int, alength: int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && 0 <= i₂
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂))
        && 0 <= alength
        && 0 <= pos
        && pos < blength₇
         ==> i₈ < alength
          || b₆[pos] < alength));

goal (forall a1: [int]int, a2: [int]int, alength: int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && 0 <= i₂
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂))
        && 0 <= alength
        && 0 <= pos
        && pos < blength₇
         ==> i₈ < alength
          || a1[b₆[pos]] == a2[b₆[pos]]));

goal (forall a1: [int]int, a2: [int]int, alength: int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && 0 <= i₂
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a1[pos] == a2[pos]
         ==> i₈ < alength
          || (exists pos2: int ::
                b₆[pos2] == pos)));

goal (forall a1: [int]int, a2: [int]int, alength: int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && 0 <= i₂
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength
                    && 0 <= i₂))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a1[pos] == a2[pos]
         ==> i₈ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < blength₇
                  && b₆[pos2] == pos)));

