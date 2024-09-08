goal (forall alength: int ::
      (0 <= alength
         ==> 1 <= alength));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, i₁: int ::
      (  0 <= alength
        && 0 < i₅
        && 1 <= i₅
        && i₅ <= alength
        && (forall i₆₀: int ::
              (  1 <= i₆₀
                && i₆₀ < i₅
                 ==> i₆₀ < alength
                  && 0 < i₆₀
                  && a₄[i₆₀] == 1 + a[0 := v][-1 + i₆₀]))
        && (forall i₆₁: int ::
                  1 <= i₆₁
                  && i₆₁ < i₅
                || a₄[i₆₁] == a[0 := v][i₆₁])
        && i₅ < alength
        && 1 <= i₁
        && i₁ < i₅ + 1
         ==> a₄[i₅ := a₄[i₅ - 1] + 1][i₁] == 1 + a[0 := v][-1 + i₁]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 < i₅
        && 1 <= i₅
        && i₅ <= alength
        && (forall i₁: int ::
              (  1 <= i₁
                && i₁ < i₅
                 ==> i₁ < alength
                  && 0 < i₁
                  && a₄[i₁] == 1 + a[0 := v][-1 + i₁]))
        && (forall i₁: int ::
                  1 <= i₁
                  && i₁ < i₅
                || a₄[i₁] == a[0 := v][i₁])
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ < alength
          || a₄[pos] <= a₄[pos + 1]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 < i₅
        && 1 <= i₅
        && i₅ <= alength
        && (forall i₁: int ::
              (  1 <= i₁
                && i₁ < i₅
                 ==> i₁ < alength
                  && 0 < i₁
                  && a₄[i₁] == 1 + a[0 := v][-1 + i₁]))
        && (forall i₁: int ::
                  1 <= i₁
                  && i₁ < i₅
                || a₄[i₁] == a[0 := v][i₁])
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ < alength
          || a₄[pos] < a₄[pos + 1]));

