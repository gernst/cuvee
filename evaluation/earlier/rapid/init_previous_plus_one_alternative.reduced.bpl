goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, i₁: int ::
      (  0 <= alength
        && 1 <= i₅
        && (forall i₄₀: int ::
              (  1 <= i₄₀
                && i₄₀ < i₅
                 ==> i₄₀ < alength
                  && a₄[i₄₀] == 1 + a[0 := v][-1 + i₄₀]))
        && (forall i₄₁: int ::
                  1 <= i₄₁
                  && i₄₁ < i₅
                || a₄[i₄₁] == a[0 := v][i₄₁])
        && i₅ < alength
        && 1 <= i₁
        && i₁ < i₅ + 1
         ==> a₄[i₅ := a₄[i₅ - 1] + 1][i₁] == 1 + a[0 := v][-1 + i₁]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 1 <= i₅
        && (forall i₁: int ::
              (  1 <= i₁
                && i₁ < i₅
                 ==> i₁ < alength
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
        && 1 <= i₅
        && (forall i₁: int ::
              (  1 <= i₁
                && i₁ < i₅
                 ==> i₁ < alength
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

