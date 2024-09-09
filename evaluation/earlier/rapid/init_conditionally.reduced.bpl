goal {:named "invariant forward"} (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int ::
      (  0 <= length
        && clength₇ + 0 == i₈ + 0
        && 0 <= clength₇
        && 0 <= i₈
        && (forall clength₁: int, i₂: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && 0 <= clength₁
                && clength₁ < clength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a[i₂] == b[i₂]
                    && i₂ < length
                    && c₆[clength₁] == i₂
                  ||   (a[i₂] == b[i₂]
                       ==> false)
                    && i₂ < length))
        && (forall clength₁: int, i₂: int ::
              (clength₁ + clength₁ == i₂ + i₂
                 ==> 0 <= clength₁
                    && clength₁ < clength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || c₆[clength₁] == c[clength₁]))
        && i₈ < length
         ==> a[i₈] == b[i₈]
          || clength₇ + 0 == i₈ + 1 + 0));

goal {:named "ensures"} (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, pos: int ::
      (  0 <= length
        && clength₇ + 0 == i₈ + 0
        && 0 <= clength₇
        && 0 <= i₈
        && (forall clength₁: int, i₂: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && 0 <= clength₁
                && clength₁ < clength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a[i₂] == b[i₂]
                    && i₂ < length
                    && c₆[clength₁] == i₂
                  ||   (a[i₂] == b[i₂]
                       ==> false)
                    && i₂ < length))
        && (forall clength₁: int, i₂: int ::
              (clength₁ + clength₁ == i₂ + i₂
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

goal {:named "ensures"} (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₆: [int]int, clength₇: int, i₈: int, pos: int ::
      (  0 <= length
        && clength₇ + 0 == i₈ + 0
        && 0 <= clength₇
        && 0 <= i₈
        && (forall clength₁: int, i₂: int ::
              (  clength₁ + clength₁ == i₂ + i₂
                && 0 <= clength₁
                && clength₁ < clength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> a[i₂] == b[i₂]
                    && i₂ < length
                    && c₆[clength₁] == i₂
                  ||   (a[i₂] == b[i₂]
                       ==> false)
                    && i₂ < length))
        && (forall clength₁: int, i₂: int ::
              (clength₁ + clength₁ == i₂ + i₂
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

