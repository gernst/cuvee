goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, i₁: int ::
      (  0 <= alength
        && 0 < i₅
        && 1 <= i₅
        && (forall i₅₄: int ::
              (  0 < i₅₄
                && 1 <= i₅₄
                && i₅₄ < i₅
                 ==> i₅₄ < alength
                  && 0 < i₅₄
                  && a₄[i₅₄] == 1 + a[0 := v][-1 + i₅₄]))
        && (forall i₅₅: int ::
              (0 < i₅₅
                 ==> 1 <= i₅₅
                    && i₅₅ < i₅
                  || a₄[i₅₅] == a[0 := v][i₅₅]))
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
        && (forall i₁: int ::
              (0 < i₁
                 ==> 1 <= i₁
                    && i₁ < i₅
                  || a₄[i₁] == a[0 := v][i₁]))
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
        && (forall i₁: int ::
              (0 < i₁
                 ==> 1 <= i₁
                    && i₁ < i₅
                  || a₄[i₁] == a[0 := v][i₁]))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ < alength
          || a₄[pos] < a₄[pos + 1]));

