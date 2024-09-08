goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, blength₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && i₈ <= alength
        && (forall blength₁₉₄: int, i₁₉₃: int ::
              (  0 <= blength₁₉₄
                && blength₁₉₄ < blength₇
                && 0 <= i₁₉₃
                && i₁₉₃ < i₈
                 ==> a1[i₁₉₃] == a2[i₁₉₃]
                    && i₁₉₃ < alength
                    && 0 <= i₁₉₃
                    && b₆[blength₁₉₄] == i₁₉₃
                  ||   (a1[i₁₉₃] == a2[i₁₉₃]
                       ==> false)
                    && i₁₉₃ < alength
                    && 0 <= i₁₉₃))
        && (forall blength₁₉₆: int, i₁₉₅: int ::
                  0 <= blength₁₉₆
                  && blength₁₉₆ < blength₇
                  && 0 <= i₁₉₅
                  && i₁₉₅ < i₈
                || b₆[blength₁₉₆] == b[blength₁₉₆])
        && i₈ < alength
        && a1[i₈] == a2[i₈]
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
        && i₈ <= alength
        && (forall blength₂₄₁: int, i₂₄₀: int ::
              (  0 <= blength₂₄₁
                && blength₂₄₁ < blength₇
                && 0 <= i₂₄₀
                && i₂₄₀ < i₈
                 ==> a1[i₂₄₀] == a2[i₂₄₀]
                    && i₂₄₀ < alength
                    && 0 <= i₂₄₀
                    && b₆[blength₂₄₁] == i₂₄₀
                  ||   (a1[i₂₄₀] == a2[i₂₄₀]
                       ==> false)
                    && i₂₄₀ < alength
                    && 0 <= i₂₄₀))
        && (forall blength₂₄₃: int, i₂₄₂: int ::
                  0 <= blength₂₄₃
                  && blength₂₄₃ < blength₇
                  && 0 <= i₂₄₂
                  && i₂₄₂ < i₈
                || b₆[blength₂₄₃] == b[blength₂₄₃])
        && i₈ < alength
        && a1[i₈] == a2[i₈]
         ==> 0 <= i₂
          || b₆[blength₇ := i₈][blength₁] == b[blength₁]));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, blength₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && i₈ <= alength
        && (forall blength₂₅₄: int, i₂₅₃: int ::
              (  0 <= blength₂₅₄
                && blength₂₅₄ < blength₇
                && 0 <= i₂₅₃
                && i₂₅₃ < i₈
                 ==> a1[i₂₅₃] == a2[i₂₅₃]
                    && i₂₅₃ < alength
                    && 0 <= i₂₅₃
                    && b₆[blength₂₅₄] == i₂₅₃
                  ||   (a1[i₂₅₃] == a2[i₂₅₃]
                       ==> false)
                    && i₂₅₃ < alength
                    && 0 <= i₂₅₃))
        && (forall blength₂₅₆: int, i₂₅₅: int ::
                  0 <= blength₂₅₆
                  && blength₂₅₆ < blength₇
                  && 0 <= i₂₅₅
                  && i₂₅₅ < i₈
                || b₆[blength₂₅₆] == b[blength₂₅₆])
        && i₈ < alength
        && a1[i₈] == a2[i₈]
         ==> i₂ < i₈ + 1
          || b₆[blength₇ := i₈][blength₁] == b[blength₁]));

goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int, b₆: [int]int, blength₇: int, i₈: int, pos: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= blength₇
        && 0 <= i₈
        && i₈ <= alength
        && (forall blength₁: int, i₂: int ::
              (  0 <= blength₁
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
                  0 <= blength₁
                  && blength₁ < blength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || b₆[blength₁] == b[blength₁])
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
        && i₈ <= alength
        && (forall blength₁: int, i₂: int ::
              (  0 <= blength₁
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
                  0 <= blength₁
                  && blength₁ < blength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || b₆[blength₁] == b[blength₁])
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
        && i₈ <= alength
        && (forall blength₁: int, i₂: int ::
              (  0 <= blength₁
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
                  0 <= blength₁
                  && blength₁ < blength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || b₆[blength₁] == b[blength₁])
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
        && i₈ <= alength
        && (forall blength₁: int, i₂: int ::
              (  0 <= blength₁
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
                  0 <= blength₁
                  && blength₁ < blength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || b₆[blength₁] == b[blength₁])
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
        && i₈ <= alength
        && (forall blength₁: int, i₂: int ::
              (  0 <= blength₁
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
                  0 <= blength₁
                  && blength₁ < blength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || b₆[blength₁] == b[blength₁])
        && 0 <= alength
        && 0 <= pos
        && pos < alength
        && a1[pos] == a2[pos]
         ==> i₈ < alength
          || (exists pos2: int ::
                  0 <= pos2
                  && pos2 < blength₇
                  && b₆[pos2] == pos)));

