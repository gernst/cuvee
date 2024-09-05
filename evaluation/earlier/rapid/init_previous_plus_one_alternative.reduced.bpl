goal (forall alength: int ::
      (0 <= alength
         ==> 1 <= alength));

goal (forall alength: int, v: int, a: [int]int, a₅: [int]int, i₆: int, x₂: int, i₁: int ::
      (  0 <= alength
        && 0 < i₆
        && 1 <= i₆
        && i₆ <= alength
        && (forall x₄₅: int, i₄₆: int ::
              (  x₄₅ == i₄₆
                && 1 <= i₄₆
                && i₄₆ < i₆
                 ==> (exists i₄₇: int ::
                        i₄₇ < alength
                        && 0 < i₄₇
                        && x₄₅ == i₄₇
                        && 1 <= i₄₇
                        && i₄₇ < i₆
                        && a₅[x₄₅] == 1 + a[0 := v][-1 + i₄₇])))
        && (forall x₄₈: int ::
                (exists i₄₉: int ::
                        x₄₈ == i₄₉
                        && 1 <= i₄₉
                        && i₄₉ < i₆)
                || a₅[x₄₈] == a[0 := v][x₄₈])
        && (forall i₅₀: int ::
              (  0 < i₅₀
                && 1 <= i₅₀
                && i₅₀ < i₆
                 ==> i₅₀ < alength))
        && i₆ < alength
        && x₂ == i₁
        && 1 <= i₁
        && i₁ < i₆ + 1
         ==> (exists i₅₁: int ::
                i₅₁ < alength
                && 0 < i₅₁
                && x₂ == i₅₁
                && 1 <= i₅₁
                && i₅₁ < i₆ + 1
                && a₅[i₆ := a₅[i₆ - 1] + 1][x₂] == 1 + a[0 := v][-1 + i₅₁])));

goal (forall alength: int, v: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
      (  0 <= alength
        && 0 < i₆
        && 1 <= i₆
        && i₆ <= alength
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 1 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                        i₁ < alength
                        && 0 < i₁
                        && x₂ == i₁
                        && 1 <= i₁
                        && i₁ < i₆
                        && a₅[x₂] == 1 + a[0 := v][-1 + i₁])))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == i₁
                        && 1 <= i₁
                        && i₁ < i₆)
                || a₅[x₂] == a[0 := v][x₂])
        && (forall i₁: int ::
              (  0 < i₁
                && 1 <= i₁
                && i₁ < i₆
                 ==> i₁ < alength))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₆ < alength
          || a₅[pos] <= a₅[pos + 1]));

goal (forall alength: int, v: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
      (  0 <= alength
        && 0 < i₆
        && 1 <= i₆
        && i₆ <= alength
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 1 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                        i₁ < alength
                        && 0 < i₁
                        && x₂ == i₁
                        && 1 <= i₁
                        && i₁ < i₆
                        && a₅[x₂] == 1 + a[0 := v][-1 + i₁])))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == i₁
                        && 1 <= i₁
                        && i₁ < i₆)
                || a₅[x₂] == a[0 := v][x₂])
        && (forall i₁: int ::
              (  0 < i₁
                && 1 <= i₁
                && i₁ < i₆
                 ==> i₁ < alength))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₆ < alength
          || a₅[pos] < a₅[pos + 1]));

