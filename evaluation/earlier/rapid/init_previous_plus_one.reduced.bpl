goal {:named "invariant forward"} (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, i₁: int ::
      (  0 <= alength
        && 0 <= i₅
        && (forall i₄₀: int ::
              (  0 <= i₄₀
                && i₄₀ < i₅
                 ==> 1 + i₄₀ < alength
                  && a₄[1 + i₄₀] == 1 + a[0 := v][i₄₀]))
        && (forall i₄₁: int ::
                  0 <= i₄₁
                  && i₄₁ < i₅
                || a₄[1 + i₄₁] == a[0 := v][1 + i₄₁])
        && i₅ + 1 < alength
        && 0 <= i₁
        && i₁ < i₅ + 1
         ==> a₄[i₅ + 1 := a₄[i₅] + 1][1 + i₁] == 1 + a[0 := v][i₁]));

goal {:named "ensures"} (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 <= i₅
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ < i₅
                 ==> 1 + i₁ < alength
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

goal {:named "ensures"} (forall alength: int, v: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= alength
        && 0 <= i₅
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ < i₅
                 ==> 1 + i₁ < alength
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

