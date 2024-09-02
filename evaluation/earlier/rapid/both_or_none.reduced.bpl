goal (forall a: [int]int, alength: int, b: [int]int, b₅: [int]int, i₆: int, j: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= alength
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                          a[i₁] == 1
                          && i₁ < alength
                          && 0 <= i₁
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < i₆
                          && b₅[x₂] == 1)
                  || (exists i₁: int ::
                        (a[i₁] == 1
                           ==> false))))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < i₆)
                || b₅[x₂] == b[x₂])
        && (forall i₁: int ::
              (  0 <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < alength))
        && 0 <= j
        && j < alength
        && 0 <= alength
         ==> i₆ < alength
          || a[j] == 1
          || b₅[j] == 0));

goal (forall a: [int]int, alength: int, b: [int]int, b₅: [int]int, i₆: int, j: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= alength
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                          a[i₁] == 1
                          && i₁ < alength
                          && 0 <= i₁
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < i₆
                          && b₅[x₂] == 1)
                  || (exists i₁: int ::
                        (a[i₁] == 1
                           ==> false))))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < i₆)
                || b₅[x₂] == b[x₂])
        && (forall i₁: int ::
              (  0 <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < alength))
        && 0 <= j
        && j < alength
        && 0 <= alength
        && a[j] == 1
         ==> i₆ < alength
          || b₅[j] == 1));

goal (forall a: [int]int, alength: int, b: [int]int, b₅: [int]int, i₆: int, j: int ::
      (  0 <= alength
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= alength
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                          a[i₁] == 1
                          && i₁ < alength
                          && 0 <= i₁
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < i₆
                          && b₅[x₂] == 1)
                  || (exists i₁: int ::
                        (a[i₁] == 1
                           ==> false))))
        && (forall x₂: int ::
                (exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < i₆)
                || b₅[x₂] == b[x₂])
        && (forall i₁: int ::
              (  0 <= i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < alength))
        && 0 <= j
        && j < alength
        && 0 <= alength
         ==> i₆ < alength
          || b₅[j] == 1
          || b₅[j] == 0));

