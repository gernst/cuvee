goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, blength₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁₈₈: int, i₁₈₇: int ::
              (  0 <= i₁₈₇
                && 0 <= blength₁₈₈
                && blength₁₈₈ < blength₇
                && 0 <= i₁₈₇
                && i₁₈₇ < i₈
                 ==> a1[i₁₈₇] == a2[i₁₈₇]
                    && i₁₈₇ < alength
                    && 0 <= i₁₈₇
                    && b₆[blength₁₈₈] == i₁₈₇
                  ||   (a1[i₁₈₇] == a2[i₁₈₇]
                       ==> false)
                    && i₁₈₇ < alength
                    && 0 <= i₁₈₇))
        && (forall blength₁₉₀: int, i₁₈₉: int ::
              (0 <= i₁₈₉
                 ==> 0 <= blength₁₉₀
                    && blength₁₉₀ < blength₇
                    && 0 <= i₁₈₉
                    && i₁₈₉ < i₈
                  || b₆[blength₁₉₀] == b[blength₁₉₀]))
        && i₈ < alength
        && a1[i₈] == a2[i₈]
        && 0 <= i₂
        && 0 <= blength₁
        && blength₁ < blength₇ + 1
        && 0 <= i₂
        && i₂ < i₈ + 1
        && a1[i₂] == a2[i₂]
         ==> b₆[blength₇ := i₈][blength₁] == i₂));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, blength₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₂₄₆: int, i₂₄₅: int ::
              (  0 <= i₂₄₅
                && 0 <= blength₂₄₆
                && blength₂₄₆ < blength₇
                && 0 <= i₂₄₅
                && i₂₄₅ < i₈
                 ==> a1[i₂₄₅] == a2[i₂₄₅]
                    && i₂₄₅ < alength
                    && 0 <= i₂₄₅
                    && b₆[blength₂₄₆] == i₂₄₅
                  ||   (a1[i₂₄₅] == a2[i₂₄₅]
                       ==> false)
                    && i₂₄₅ < alength
                    && 0 <= i₂₄₅))
        && (forall blength₂₄₈: int, i₂₄₇: int ::
              (0 <= i₂₄₇
                 ==> 0 <= blength₂₄₈
                    && blength₂₄₈ < blength₇
                    && 0 <= i₂₄₇
                    && i₂₄₇ < i₈
                  || b₆[blength₂₄₈] == b[blength₂₄₈]))
        && i₈ < alength
        && a1[i₈] == a2[i₈]
        && 0 <= i₂
         ==> i₂ < i₈ + 1
          || b₆[blength₇ := i₈][blength₁] == b[blength₁]));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
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
        && (forall blength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= blength₁
                    && blength₁ < blength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || b₆[blength₁] == b[blength₁]))
        && 0 <= alength
        && 0 <= pos
        && pos < blength₇
         ==> i₈ < alength
          || 0 <= b₆[pos]));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
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
        && (forall blength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= blength₁
                    && blength₁ < blength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || b₆[blength₁] == b[blength₁]))
        && 0 <= alength
        && 0 <= pos
        && pos < blength₇
         ==> i₈ < alength
          || b₆[pos] < alength));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
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
        && (forall blength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= blength₁
                    && blength₁ < blength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || b₆[blength₁] == b[blength₁]))
        && 0 <= alength
        && 0 <= pos
        && pos < blength₇
         ==> i₈ < alength
          || a1[b₆[pos]] == a2[b₆[pos]]));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
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
        && (forall blength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= blength₁
                    && blength₁ < blength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || b₆[blength₁] == b[blength₁]))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a1[pos] == a2[pos]
         ==> i₈ < alength
          || (exists pos2: int ::
                b₆[pos2] == pos)));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
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
        && (forall blength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= blength₁
                    && blength₁ < blength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || b₆[blength₁] == b[blength₁]))
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a1[pos] == a2[pos]
         ==> i₈ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < blength₇
                  && b₆[pos2] == pos)));

