goal (forall a: [int]int, b: [int]int, length: int, c: [int]int, c₇: [int]int, clength₈: int, i₉: int, pos: int ::
      (  0 <= length
        && 0 <= i₉
        && 0 <= clength₈
        && 0 <= i₉
        && i₉ <= length
        && (forall x₃: int, clength₁: int ::
              (  x₃ == clength₁
                && 0 <= clength₁
                && clength₁ < clength₈
                 ==> (exists clength₁: int, i₂: int ::
                        a[i₂] == b[i₂]
                        && i₂ < length
                        && 0 <= i₂
                        && x₃ == clength₁
                        && 0 <= clength₁
                        && clength₁ < clength₈
                        && 0 <= i₂
                        && i₂ < i₉
                        && c₇[x₃] == i₂)))
        && (forall x₃: int ::
                (exists clength₁: int ::
                        x₃ == clength₁
                        && 0 <= clength₁
                        && clength₁ < clength₈)
                || c₇[x₃] == c[x₃])
        && (forall clength₁: int, i₂: int ::
              (  0 <= i₂
                && clength₁ <= clength₁
                && i₂ <= i₂
                && 0 <= clength₁
                && clength₁ < clength₈
                && 0 <= i₂
                && i₂ < i₉
                 ==> i₂ < length))
        && 0 <= pos
        && pos < clength₈
        && 0 <= length
         ==> i₉ < length
          || pos <= c₇[pos]));

