goal (forall b: [int]int, blength: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
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
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < blength))
        && 0 <= pos
        && pos < blength
        && 0 <= blength
         ==> i₆ < blength
          || a₅[pos] <= 0));

goal (forall b: [int]int, blength: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
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
                && 0 <= i₁
                && i₁ < i₆
                 ==> i₁ < blength))
        && 0 <= pos
        && pos < blength
        && 0 <= blength
         ==> i₆ < blength
          || a₅[pos] == 0
          || a₅[pos] == b[pos]));

