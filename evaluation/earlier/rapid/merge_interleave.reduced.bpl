goal {:named "ensures"} (forall a: [int]int, b: [int]int, alength: int, c: [int]int, c₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 <= i₅
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ < i₅
                 ==> i₁ < alength
                  && c₄[1 + 2 * i₁] == b[i₁]
                  &&   2 * i₁ == 1 + 2 * i₁
                    || c₄[2 * i₁] == a[i₁]))
        && (forall i₁: int ::
                  0 <= i₁
                  && i₁ < i₅
                ||   c₄[1 + 2 * i₁] == c[1 + 2 * i₁]
                  && c₄[2 * i₁] == c[2 * i₁])
         ==> i₅ < alength
          || (exists j: int ::
                (  0 <= alength
                  && 0 <= pos
                  && pos < alength
                   ==> c₄[pos] == a[j]
                    || c₄[pos] == b[j]))));

