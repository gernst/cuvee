goal (forall alength: int, a: [int]int, a₅: [int]int, i₆: int, x₂: int, i₁: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= alength
        && (forall x₃₆: int, i₃₇: int ::
              (  x₃₆ == i₃₇
                && 0 <= i₃₇
                && i₃₇ < i₆
                 ==> (exists i₃₈: int ::
                        a₅[i₃₈] < 0
                        && i₃₈ < alength
                        && 0 <= i₃₈
                        && x₃₆ == i₃₈
                        && 0 <= i₃₈
                        && i₃₈ < i₆
                        && a₅[x₃₆] == 0)))
        && (forall x₃₉: int ::
                (exists i₄₀: int ::
                        x₃₉ == i₄₀
                        && 0 <= i₄₀
                        && i₄₀ < i₆)
                || a₅[x₃₉] == a[x₃₉])
        && (forall i₄₁: int ::
              (  0 <= i₄₁
                && 0 <= i₄₁
                && i₄₁ < i₆
                 ==> i₄₁ < alength))
        && i₆ < alength
        && a₅[i₆] < 0
        && x₂ == i₁
        && 0 <= i₁
        && i₁ < i₆ + 1
         ==> (exists i₄₂: int ::
                a₅[i₆ := 0][i₄₂] < 0
                && i₄₂ < alength
                && 0 <= i₄₂
                && x₂ == i₄₂
                && 0 <= i₄₂
                && i₄₂ < i₆ + 1
                && a₅[i₆ := 0][x₂] == 0)));

goal (forall alength: int, a: [int]int, a₅: [int]int, i₆: int, x₂: int, i₁: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= alength
        && (forall x₆₇: int, i₆₈: int ::
              (  x₆₇ == i₆₈
                && 0 <= i₆₈
                && i₆₈ < i₆
                 ==> (exists i₆₉: int ::
                        a₅[i₆₉] < 0
                        && i₆₉ < alength
                        && 0 <= i₆₉
                        && x₆₇ == i₆₉
                        && 0 <= i₆₉
                        && i₆₉ < i₆
                        && a₅[x₆₇] == 0)))
        && (forall x₇₀: int ::
                (exists i₇₁: int ::
                        x₇₀ == i₇₁
                        && 0 <= i₇₁
                        && i₇₁ < i₆)
                || a₅[x₇₀] == a[x₇₀])
        && (forall i₇₂: int ::
              (  0 <= i₇₂
                && 0 <= i₇₂
                && i₇₂ < i₆
                 ==> i₇₂ < alength))
        && i₆ < alength
        && x₂ == i₁
        && 0 <= i₁
        && i₁ < i₆ + 1
         ==> a₅[i₆] < 0
          || (exists i₇₃: int ::
                  a₅[i₇₃] < 0
                  && i₇₃ < alength
                  && 0 <= i₇₃
                  && x₂ == i₇₃
                  && 0 <= i₇₃
                  && i₇₃ < i₆ + 1
                  && a₅[x₂] == 0)));

