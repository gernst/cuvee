goal (forall b: [int]int, blength: int, a: [int]int, a₇: [int]int, alength₈: int, i₉: int, k: int ::
      (  0 <= blength
        && 0 <= i₉
        && 0 <= alength₈
        && 0 <= i₉
        && i₉ <= blength
        && (forall x₃: int, alength₁: int ::
              (  x₃ == alength₁
                && 0 <= alength₁
                && alength₁ < alength₈
                 ==> (exists i₂: int ::
                      (b[i₂] == 0
                         ==> false))))
        && (forall x₃: int ::
                (exists alength₁: int ::
                        x₃ == alength₁
                        && 0 <= alength₁
                        && alength₁ < alength₈)
                || a₇[x₃] == a[x₃])
        && (forall alength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= alength₁
                && alength₁ < alength₈
                && 0 <= i₂
                && i₂ < i₉
                 ==> i₂ < blength))
        && 0 <= blength
        && 0 <= k
        && k < alength₈
        && a₇[k] == 0
         ==> i₉ < blength));

goal (forall b: [int]int, blength: int, a: [int]int, a₇: [int]int, alength₈: int, i₉: int, k: int ::
      (  0 <= blength
        && 0 <= i₉
        && 0 <= alength₈
        && 0 <= i₉
        && i₉ <= blength
        && (forall x₃: int, alength₁: int ::
              (  x₃ == alength₁
                && 0 <= alength₁
                && alength₁ < alength₈
                 ==> (exists i₂: int ::
                      (b[i₂] == 0
                         ==> false))))
        && (forall x₃: int ::
                (exists alength₁: int ::
                        x₃ == alength₁
                        && 0 <= alength₁
                        && alength₁ < alength₈)
                || a₇[x₃] == a[x₃])
        && (forall alength₁: int, i₂: int ::
              (  0 <= i₂
                && 0 <= alength₁
                && alength₁ < alength₈
                && 0 <= i₂
                && i₂ < i₉
                 ==> i₂ < blength))
         ==> i₉ < blength
          || (exists l: int ::
                (  0 <= k
                  && 0 <= blength
                  && k < alength₈
                   ==> a₇[k] == b[l]))));

