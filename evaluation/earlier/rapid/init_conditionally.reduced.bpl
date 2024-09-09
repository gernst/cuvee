goal (forall a: [int]int, b: [int]int, length: int, c₆: [int]int, clength₇: int, i₈: int, clength₁: int, i₂: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && (forall clength₁₆₀: int, i₁₅₉: int ::
              (  0 <= i₁₅₉
                && 0 <= clength₁₆₀
                && clength₁₆₀ < clength₇
                && 0 <= i₁₅₉
                && i₁₅₉ < i₈
                 ==> a[i₁₅₉] == b[i₁₅₉]
                    && i₁₅₉ < length
                    && 0 <= i₁₅₉
                    && c₆[clength₁₆₀] == i₁₅₉
                  ||   (a[i₁₅₉] == b[i₁₅₉]
                       ==> false)
                    && i₁₅₉ < length
                    && 0 <= i₁₅₉))
        && i₈ < length
        && a[i₈] == b[i₈]
        && 0 <= i₂
        && 0 <= clength₁
        && clength₁ < clength₇ + 1
        && 0 <= i₂
        && i₂ < i₈ + 1
        && a[i₂] == b[i₂]
         ==> c₆[clength₇ := i₈][clength₁] == i₂));

goal (forall a: [int]int, b: [int]int, length: int, c₆: [int]int, clength₇: int, i₈: int, pos: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && (forall clength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= clength₁
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
        && 0 <= pos
        && pos < clength₇
        && 0 <= length
         ==> i₈ < length
          || a[c₆[pos]] == b[c₆[pos]]));

goal (forall a: [int]int, b: [int]int, length: int, c₆: [int]int, clength₇: int, i₈: int, pos: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && (forall clength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= clength₁
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
        && 0 <= pos
        && pos < clength₇
        && 0 <= length
         ==> i₈ < length
          || pos <= c₆[pos]));

