goal (forall blength: int, b: [int]int, a: [int]int, a₅: [int]int, i₆: int, k: int ::
      (  0 <= blength
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= blength
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                          b[i₁] >= 0
                          && i₁ < blength
                          && 0 <= i₁
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < i₆
                          && a₅[x₂] == b[i₁])
                  || (exists i₁: int ::
                        (b[i₁] >= 0
                           ==> false))))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < i₆)
                || a₅[x₂] == a[x₂])
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < blength))
        && 0 <= k
        && k < blength
         ==> i₆ < blength
          || a₅[k] == b[k]
          || a₅[k] == 0 - b[k]));

goal (forall blength: int, b: [int]int, a: [int]int, a₅: [int]int, i₆: int, k: int ::
      (  0 <= blength
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= blength
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                          b[i₁] >= 0
                          && i₁ < blength
                          && 0 <= i₁
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < i₆
                          && a₅[x₂] == b[i₁])
                  || (exists i₁: int ::
                        (b[i₁] >= 0
                           ==> false))))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < i₆)
                || a₅[x₂] == a[x₂])
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < blength))
        && 0 <= k
        && k < blength
         ==> i₆ < blength
          || 0 <= a₅[k]));

