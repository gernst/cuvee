goal {:named "invariant forward"} (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int ::
      (  0 <= alength
        && 0 + blength₇ == i₈ + 0
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  blength₁ + blength₁ == i₂ + i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength))
        && (forall blength₁: int, i₂: int ::
              (blength₁ + blength₁ == i₂ + i₂
                 ==> 0 <= blength₁
                    && blength₁ < blength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || b₆[blength₁] == b[blength₁]))
        && i₈ < alength
         ==> a1[i₈] == a2[i₈]
          || 0 + blength₇ == i₈ + 1 + 0));

goal {:named "ensures"} (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 + blength₇ == i₈ + 0
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  blength₁ + blength₁ == i₂ + i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength))
        && (forall blength₁: int, i₂: int ::
              (blength₁ + blength₁ == i₂ + i₂
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

goal {:named "ensures"} (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 + blength₇ == i₈ + 0
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  blength₁ + blength₁ == i₂ + i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength))
        && (forall blength₁: int, i₂: int ::
              (blength₁ + blength₁ == i₂ + i₂
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

goal {:named "ensures"} (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 + blength₇ == i₈ + 0
        && 0 <= blength₇
        && 0 <= i₈
        && (forall blength₁: int, i₂: int ::
              (  blength₁ + blength₁ == i₂ + i₂
                && 0 <= blength₁
                && blength₁ < blength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a1[i₂] == a2[i₂]
                    && i₂ < alength
                    && b₆[blength₁] == i₂
                  ||   (a1[i₂] == a2[i₂]
                       ==> false)
                    && i₂ < alength))
        && (forall blength₁: int, i₂: int ::
              (blength₁ + blength₁ == i₂ + i₂
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

