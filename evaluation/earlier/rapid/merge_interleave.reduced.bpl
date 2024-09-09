goal (forall a: [int]int, b: [int]int, alength: int, c₅: [int]int, i₆: int, pos: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && (forall i₁: int ::
              (  0 <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < alength
                  && 0 <= i₁
                  && (forall x₂: int ::
                            x₂ == 1 + 2 * i₁
                            && 0 <= i₁
                            && i₁ < i₆
                            && c₅[x₂] == b[i₁]
                          ||   (x₂ == 1 + 2 * i₁
                               ==> false)
                            && (x₂ == 2 * i₁
                               ==> 0 <= i₁
                                && i₁ < i₆
                                && c₅[x₂] == a[i₁]))))
         ==> i₆ < alength
          || (exists j: int ::
                (  0 <= alength
                  && 0 <= pos
                  && pos < alength
                   ==> c₅[pos] == a[j]
                    || c₅[pos] == b[j]))));

