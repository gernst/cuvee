goal (forall alength: int, a: [int]int, a₄: [int]int, i₅: int, i₁: int ::
      (  0 <= alength
        && 0 <= i₅
        && 0 <= i₅
        && (forall i₃₅: int ::
              (  0 <= i₃₅
                && 0 <= i₃₅
                && i₃₅ < i₅
                 ==> i₃₅ < alength
                  && 0 <= i₃₅
                  && a₄[i₃₅] == 1 + a[i₃₅]))
        && i₅ < alength
        && 0 <= i₁
        && 0 <= i₁
        && i₁ < i₅ + 1
         ==> a₄[i₅ := a₄[i₅] + 1][i₁] == 1 + a[i₁]));

