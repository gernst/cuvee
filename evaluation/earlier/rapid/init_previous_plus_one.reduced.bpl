goal (forall alength: int ::
      (0 <= alength
         ==> 1 + 0 <= alength));

goal (forall alength: int, v: int, a: [int]int, a₅: [int]int, i₆: int, x₂: int, i₁: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && 1 + i₆ <= alength
        && (forall x₃₉: int, i₄₀: int ::
              (  x₃₉ == 1 + i₄₀
                && 0 <= i₄₀
                && i₄₀ < i₆
                 ==> (exists i₄₁: int ::
                        1 + i₄₁ < alength
                        && 0 <= i₄₁
                        && x₃₉ == 1 + i₄₁
                        && 0 <= i₄₁
                        && i₄₁ < i₆
                        && a₅[x₃₉] == 1 + a[0 := v][i₄₁])))
        && (forall x₄₂: int ::
                (exists i₄₃: int ::
                        x₄₂ == 1 + i₄₃
                        && 0 <= i₄₃
                        && i₄₃ < i₆)
                || a₅[x₄₂] == a[0 := v][x₄₂])
        && (forall i₄₄: int ::
              (  0 <= i₄₄
                && i₄₄ <= i₄₄
                && 0 <= i₄₄
                && i₄₄ < i₆
                 ==> 1 + i₄₄ < alength))
        && i₆ + 1 < alength
        && x₂ == 1 + i₁
        && 0 <= i₁
        && i₁ < i₆ + 1
         ==> (exists i₄₅: int ::
                1 + i₄₅ < alength
                && 0 <= i₄₅
                && x₂ == 1 + i₄₅
                && 0 <= i₄₅
                && i₄₅ < i₆ + 1
                && a₅[i₆ + 1 := a₅[i₆] + 1][x₂] == 1 + a[0 := v][i₄₅])));

goal (forall alength: int, v: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && 1 + i₆ <= alength
        && (forall x₂: int, i₁: int ::
              (  x₂ == 1 + i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                        1 + i₁ < alength
                        && 0 <= i₁
                        && x₂ == 1 + i₁
                        && 0 <= i₁
                        && i₁ < i₆
                        && a₅[x₂] == 1 + a[0 := v][i₁])))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == 1 + i₁
                        && 0 <= i₁
                        && i₁ < i₆)
                || a₅[x₂] == a[0 := v][x₂])
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> 1 + i₁ < alength))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₆ + 1 < alength
          || a₅[pos] <= a₅[pos + 1]));

goal (forall alength: int, v: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && 1 + i₆ <= alength
        && (forall x₂: int, i₁: int ::
              (  x₂ == 1 + i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                        1 + i₁ < alength
                        && 0 <= i₁
                        && x₂ == 1 + i₁
                        && 0 <= i₁
                        && i₁ < i₆
                        && a₅[x₂] == 1 + a[0 := v][i₁])))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == 1 + i₁
                        && 0 <= i₁
                        && i₁ < i₆)
                || a₅[x₂] == a[0 := v][x₂])
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> 1 + i₁ < alength))
        && 0 <= pos
        && pos + 1 < alength
        && 0 <= alength
         ==> i₆ + 1 < alength
          || a₅[pos] < a₅[pos + 1]));

