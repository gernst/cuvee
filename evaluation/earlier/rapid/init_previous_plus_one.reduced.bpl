goal (forall alength: int ::
      (0 <= alength
         ==> 1 + 0 <= alength));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, i₁: int ::
      (  0 <= alength
        && 0 <= i₅
        && 0 <= i₅
        && 1 + i₅ <= alength
        && (forall i₅₄: int ::
              (  0 <= i₅₄
                && i₅₄ < i₅
                 ==> 1 + i₅₄ < alength
                  && 0 <= i₅₄
                  && a₄[1 + i₅₄] == 1 + a[0 := v][i₅₄]))
        && (forall i₅₅: int ::
                  0 <= i₅₅
                  && i₅₅ < i₅
                || a₄[1 + i₅₅] == a[0 := v][1 + i₅₅])
        && i₅ + 1 < alength
        && 0 <= i₁
        && i₁ < i₅ + 1
         ==> a₄[i₅ + 1 := a₄[i₅] + 1][1 + i₁] == 1 + a[0 := v][i₁]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 <= i₅
        && 0 <= i₅
        && 1 + i₅ <= alength
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ < i₅
                 ==> 1 + i₁ < alength
                  && 0 <= i₁
                  && a₄[1 + i₁] == 1 + a[0 := v][i₁]))
        && (forall i₁: int ::
                  0 <= i₁
                  && i₁ < i₅
                || a₄[1 + i₁] == a[0 := v][1 + i₁])
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ + 1 < alength
          || a₄[pos] <= a₄[pos + 1]));

goal (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 <= i₅
        && 0 <= i₅
        && 1 + i₅ <= alength
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ < i₅
                 ==> 1 + i₁ < alength
                  && 0 <= i₁
                  && a₄[1 + i₁] == 1 + a[0 := v][i₁]))
        && (forall i₁: int ::
                  0 <= i₁
                  && i₁ < i₅
                || a₄[1 + i₁] == a[0 := v][1 + i₁])
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₅ + 1 < alength
          || a₄[pos] < a₄[pos + 1]));

