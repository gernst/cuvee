goal (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, clength₁: int, i₂: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && i₈ <= length
        && (forall clength₁₉₄: int, i₁₉₃: int ::
              (  0 <= clength₁₉₄
                && clength₁₉₄ < clength₇
                && 0 <= i₁₉₃
                && i₁₉₃ < i₈
                 ==> a[i₁₉₃] == b[i₁₉₃]
                    && i₁₉₃ < length
                    && 0 <= i₁₉₃
                    && c₆[clength₁₉₄] == i₁₉₃
                  ||   (a[i₁₉₃] == b[i₁₉₃]
                       ==> false)
                    && i₁₉₃ < length
                    && 0 <= i₁₉₃))
        && (forall clength₁₉₆: int, i₁₉₅: int ::
                  0 <= clength₁₉₆
                  && clength₁₉₆ < clength₇
                  && 0 <= i₁₉₅
                  && i₁₉₅ < i₈
                || c₆[clength₁₉₆] == c[clength₁₉₆])
        && i₈ < length
        && a[i₈] == b[i₈]
        && 0 <= clength₁
        && clength₁ < clength₇ + 1
        && 0 <= i₂
        && i₂ < i₈ + 1
        && a[i₂] == b[i₂]
         ==> c₆[clength₇ := i₈][clength₁] == i₂));

goal (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, clength₁: int, i₂: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && i₈ <= length
        && (forall clength₂₄₁: int, i₂₄₀: int ::
              (  0 <= clength₂₄₁
                && clength₂₄₁ < clength₇
                && 0 <= i₂₄₀
                && i₂₄₀ < i₈
                 ==> a[i₂₄₀] == b[i₂₄₀]
                    && i₂₄₀ < length
                    && 0 <= i₂₄₀
                    && c₆[clength₂₄₁] == i₂₄₀
                  ||   (a[i₂₄₀] == b[i₂₄₀]
                       ==> false)
                    && i₂₄₀ < length
                    && 0 <= i₂₄₀))
        && (forall clength₂₄₃: int, i₂₄₂: int ::
                  0 <= clength₂₄₃
                  && clength₂₄₃ < clength₇
                  && 0 <= i₂₄₂
                  && i₂₄₂ < i₈
                || c₆[clength₂₄₃] == c[clength₂₄₃])
        && i₈ < length
        && a[i₈] == b[i₈]
         ==> 0 <= i₂
          || c₆[clength₇ := i₈][clength₁] == c[clength₁]));

goal (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, clength₁: int, i₂: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && i₈ <= length
        && (forall clength₂₅₄: int, i₂₅₃: int ::
              (  0 <= clength₂₅₄
                && clength₂₅₄ < clength₇
                && 0 <= i₂₅₃
                && i₂₅₃ < i₈
                 ==> a[i₂₅₃] == b[i₂₅₃]
                    && i₂₅₃ < length
                    && 0 <= i₂₅₃
                    && c₆[clength₂₅₄] == i₂₅₃
                  ||   (a[i₂₅₃] == b[i₂₅₃]
                       ==> false)
                    && i₂₅₃ < length
                    && 0 <= i₂₅₃))
        && (forall clength₂₅₆: int, i₂₅₅: int ::
                  0 <= clength₂₅₆
                  && clength₂₅₆ < clength₇
                  && 0 <= i₂₅₅
                  && i₂₅₅ < i₈
                || c₆[clength₂₅₆] == c[clength₂₅₆])
        && i₈ < length
        && a[i₈] == b[i₈]
         ==> i₂ < i₈ + 1
          || c₆[clength₇ := i₈][clength₁] == c[clength₁]));

goal (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, pos: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && i₈ <= length
        && (forall clength₁: int, i₂: int ::
              (  0 <= clength₁
                && clength₁ < clength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a[i₂] == b[i₂]
                    && i₂ < length
                    && 0 <= i₂
                    && c₆[clength₁] == i₂
                  ||   (a[i₂] == b[i₂]
                       ==> false)
                    && i₂ < length
                    && 0 <= i₂))
        && (forall clength₁: int, i₂: int ::
                  0 <= clength₁
                  && clength₁ < clength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || c₆[clength₁] == c[clength₁])
        && 0 <= pos
        && pos < clength₇
        && 0 <= length
         ==> i₈ < length
          || a[c₆[pos]] == b[c₆[pos]]));

goal (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, pos: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && i₈ <= length
        && (forall clength₁: int, i₂: int ::
              (  0 <= clength₁
                && clength₁ < clength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a[i₂] == b[i₂]
                    && i₂ < length
                    && 0 <= i₂
                    && c₆[clength₁] == i₂
                  ||   (a[i₂] == b[i₂]
                       ==> false)
                    && i₂ < length
                    && 0 <= i₂))
        && (forall clength₁: int, i₂: int ::
                  0 <= clength₁
                  && clength₁ < clength₇
                  && 0 <= i₂
                  && i₂ < i₈
                || c₆[clength₁] == c[clength₁])
        && 0 <= pos
        && pos < clength₇
        && 0 <= length
         ==> i₈ < length
          || pos <= c₆[pos]));

