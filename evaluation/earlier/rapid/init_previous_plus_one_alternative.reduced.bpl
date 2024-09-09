goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, i₁: int ::
      (  0 <= alength
        && 0 < i₅
        && 1 <= i₅
        && (forall i₄₆: int ::
              (  0 < i₄₆
                && 1 <= i₄₆
                && i₄₆ < i₅
                 ==> i₄₆ < alength
                  && 0 < i₄₆
                  && a₄[i₄₆] == 1 + a[0 := v][-1 + i₄₆]))
        && i₅ < alength
        && 0 < i₁
        && 1 <= i₁
        && i₁ < i₅ + 1
         ==> a₄[i₅ := a₄[i₅ - 1] + 1][i₁] == 1 + a[0 := v][-1 + i₁]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 < i₅
        && 1 <= i₅
        && (forall i₁: int ::
              (  0 < i₁
                && 1 <= i₁
                && i₁ < i₅
                 ==> i₁ < alength
                  && 0 < i₁
                  && a₄[i₁] == 1 + a[0 := v][-1 + i₁]))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ < alength
          || a₄[pos] <= a₄[pos + 1]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 < i₅
        && 1 <= i₅
        && (forall i₁: int ::
              (  0 < i₁
                && 1 <= i₁
                && i₁ < i₅
                 ==> i₁ < alength
                  && 0 < i₁
                  && a₄[i₁] == 1 + a[0 := v][-1 + i₁]))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ < alength
          || a₄[pos] < a₄[pos + 1]));

