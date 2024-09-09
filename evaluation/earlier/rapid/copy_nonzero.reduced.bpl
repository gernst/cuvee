goal {:named "invariant forward"} (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int ::
      (  0 <= blength
        && 0 + alength₇ == i₈ + 0
        && 0 <= alength₇
        && 0 <= i₈
        && (forall alength₁: int, i₂: int ::
              (  alength₁ + alength₁ == i₂ + i₂
                && 0 <= alength₁
                && alength₁ < alength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> (b[i₂] == 0
                       ==> false)
                    && i₂ < blength
                    && a₆[alength₁] == b[i₂]
                  ||   b[i₂] == 0
                    && i₂ < blength))
        && (forall alength₁: int, i₂: int ::
              (alength₁ + alength₁ == i₂ + i₂
                 ==> 0 <= alength₁
                    && alength₁ < alength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || a₆[alength₁] == a[alength₁]))
        && i₈ < blength
        && b[i₈] == 0
         ==> 0 + alength₇ == i₈ + 1 + 0));

goal {:named "ensures"} (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, k: int ::
      (  0 <= blength
        && 0 + alength₇ == i₈ + 0
        && 0 <= alength₇
        && 0 <= i₈
        && (forall alength₁: int, i₂: int ::
              (  alength₁ + alength₁ == i₂ + i₂
                && 0 <= alength₁
                && alength₁ < alength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> (b[i₂] == 0
                       ==> false)
                    && i₂ < blength
                    && a₆[alength₁] == b[i₂]
                  ||   b[i₂] == 0
                    && i₂ < blength))
        && (forall alength₁: int, i₂: int ::
              (alength₁ + alength₁ == i₂ + i₂
                 ==> 0 <= alength₁
                    && alength₁ < alength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || a₆[alength₁] == a[alength₁]))
        && 0 <= blength
        && 0 <= k
        && k < alength₇
        && a₆[k] == 0
         ==> i₈ < blength));

goal {:named "ensures"} (forall b: [int]int, blength: int, a: [int]int, a₆: [int]int, alength₇: int, i₈: int, k: int ::
      (  0 <= blength
        && 0 + alength₇ == i₈ + 0
        && 0 <= alength₇
        && 0 <= i₈
        && (forall alength₁: int, i₂: int ::
              (  alength₁ + alength₁ == i₂ + i₂
                && 0 <= alength₁
                && alength₁ < alength₇
                && 0 <= i₂
                && i₂ < i₈
                 ==> (b[i₂] == 0
                       ==> false)
                    && i₂ < blength
                    && a₆[alength₁] == b[i₂]
                  ||   b[i₂] == 0
                    && i₂ < blength))
        && (forall alength₁: int, i₂: int ::
              (alength₁ + alength₁ == i₂ + i₂
                 ==> 0 <= alength₁
                    && alength₁ < alength₇
                    && 0 <= i₂
                    && i₂ < i₈
                  || a₆[alength₁] == a[alength₁]))
         ==> i₈ < blength
          || (exists l: int ::
                (  0 <= k
                  && 0 <= blength
                  && k < alength₇
                   ==> a₆[k] == b[l]))));

