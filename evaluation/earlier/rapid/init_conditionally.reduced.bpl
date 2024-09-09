goal (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, clength₁: int, i₂: int ::
      (  0 <= length
        && 0 <= i₈
        && 0 <= clength₇
        && 0 <= i₈
        && (forall clength₁₈₈: int, i₁₈₇: int ::
              (  0 <= i₁₈₇
                && 0 <= clength₁₈₈
                && clength₁₈₈ < clength₇
                && 0 <= i₁₈₇
                && i₁₈₇ < i₈
                 ==> a[i₁₈₇] == b[i₁₈₇]
                    && i₁₈₇ < length
                    && 0 <= i₁₈₇
                    && c₆[clength₁₈₈] == i₁₈₇
                  ||   (a[i₁₈₇] == b[i₁₈₇]
                       ==> false)
                    && i₁₈₇ < length
                    && 0 <= i₁₈₇))
        && (forall clength₁₉₀: int, i₁₈₉: int ::
              (0 <= i₁₈₉
                 ==> 0 <= clength₁₉₀
                    && clength₁₉₀ < clength₇
                    && 0 <= i₁₈₉
                    && i₁₈₉ < i₈
                  || c₆[clength₁₉₀] == c[clength₁₉₀]))
        && i₈ < length
        && a[i₈] == b[i₈]
        && 0 <= i₂
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
        && (forall clength₂₄₆: int, i₂₄₅: int ::
              (  0 <= i₂₄₅
                && 0 <= clength₂₄₆
                && clength₂₄₆ < clength₇
                && 0 <= i₂₄₅
                && i₂₄₅ < i₈
                 ==> a[i₂₄₅] == b[i₂₄₅]
                    && i₂₄₅ < length
                    && 0 <= i₂₄₅
                    && c₆[clength₂₄₆] == i₂₄₅
                  ||   (a[i₂₄₅] == b[i₂₄₅]
                       ==> false)
                    && i₂₄₅ < length
                    && 0 <= i₂₄₅))
        && (forall clength₂₄₈: int, i₂₄₇: int ::
              (0 <= i₂₄₇
                 ==> 0 <= clength₂₄₈
                    && clength₂₄₈ < clength₇
                    && 0 <= i₂₄₇
                    && i₂₄₇ < i₈
                  || c₆[clength₂₄₈] == c[clength₂₄₈]))
        && i₈ < length
        && a[i₈] == b[i₈]
        && 0 <= i₂
         ==> i₂ < i₈ + 1
          || c₆[clength₇ := i₈][clength₁] == c[clength₁]));

goal (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, pos: int ::
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
        && (forall clength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= clength₁
                    && clength₁ < clength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || c₆[clength₁] == c[clength₁]))
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
        && (forall clength₁: int, i₂: int ::
              (0 <= i₂
                 ==> 0 <= clength₁
                    && clength₁ < clength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || c₆[clength₁] == c[clength₁]))
        && 0 <= pos
        && pos < clength₇
        && 0 <= length
         ==> i₈ < length
          || pos <= c₆[pos]));

