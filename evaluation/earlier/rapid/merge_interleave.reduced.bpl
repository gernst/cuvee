goal (forall a: [int]int, b: [int]int, alength: int, c: [int]int, c₅: [int]int, i₆: int, pos: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= alength
        && (forall x₂: int, i₁: int ::
              (  (x₂ == 1 + 2 * i₁
                   ==> 0 <= i₁
                    && i₁ < i₆)
                &&   x₂ == 1 + 2 * i₁
                  ||   x₂ == 2 * i₁
                    && 0 <= i₁
                    && i₁ < i₆
                 ==> (exists i₁: int ::
                        i₁ < alength
                        && 0 <= i₁
                        && if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < i₆ && c₅[x₂] == b[i₁] else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < i₆ && c₅[x₂] == a[i₁])))
        && (forall x₂: int ::
                (exists i₁: int ::
                      if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < i₆ else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < i₆)
                || c₅[x₂] == c[x₂])
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < alength))
         ==> i₆ < alength
          || (exists j: int ::
                (  0 <= alength
                  && 0 <= pos
                  && pos < alength
                   ==> c₅[pos] == a[j]
                    || c₅[pos] == b[j]))));

