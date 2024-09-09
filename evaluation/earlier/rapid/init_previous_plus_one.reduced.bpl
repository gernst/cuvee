goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, i₁: int ::
      (  0 <= alength
        && 0 <= i₅
        && 0 <= i₅
        && (forall i₄₈: int ::
              (  0 <= i₄₈
                && 0 <= i₄₈
                && i₄₈ < i₅
                 ==> 1 + i₄₈ < alength
                  && 0 <= i₄₈
                  && a₄[1 + i₄₈] == 1 + a[0 := v][i₄₈]))
        && (forall i₄₉: int ::
              (0 <= i₄₉
                 ==> 0 <= i₄₉
                    && i₄₉ < i₅
                  || a₄[1 + i₄₉] == a[0 := v][1 + i₄₉]))
        && i₅ + 1 < alength
        && 0 <= i₁
        && 0 <= i₁
        && i₁ < i₅ + 1
         ==> a₄[i₅ + 1 := a₄[i₅] + 1][1 + i₁] == 1 + a[0 := v][i₁]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 <= i₅
        && 0 <= i₅
        && (forall i₁: int ::
              (  0 <= i₁
                && 0 <= i₁
                && i₁ < i₅
                 ==> 1 + i₁ < alength
                  && 0 <= i₁
                  && a₄[1 + i₁] == 1 + a[0 := v][i₁]))
        && (forall i₁: int ::
              (0 <= i₁
                 ==> 0 <= i₁
                    && i₁ < i₅
                  || a₄[1 + i₁] == a[0 := v][1 + i₁]))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ + 1 < alength
          || a₄[pos] <= a₄[pos + 1]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 <= i₅
        && 0 <= i₅
        && (forall i₁: int ::
              (  0 <= i₁
                && 0 <= i₁
                && i₁ < i₅
                 ==> 1 + i₁ < alength
                  && 0 <= i₁
                  && a₄[1 + i₁] == 1 + a[0 := v][i₁]))
        && (forall i₁: int ::
              (0 <= i₁
                 ==> 0 <= i₁
                    && i₁ < i₅
                  || a₄[1 + i₁] == a[0 := v][1 + i₁]))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ + 1 < alength
          || a₄[pos] < a₄[pos + 1]));

