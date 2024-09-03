goal (forall b: [int]int, length: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
      (  0 <= length
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= length
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                        i₁ < length
                        && (b[i₁] == 0
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
                 ==> i₁ < length
                  && (b[i₁] == 0
                     ==> false)))
        && 0 <= length
        && 0 <= pos
        && pos < i₆
         ==> i₆ < length
          || a₅[pos] == b[pos]));

goal (forall b: [int]int, length: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
      (  0 <= length
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= length
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                        i₁ < length
                        && (b[i₁] == 0
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
                 ==> i₁ < length
                  && (b[i₁] == 0
                     ==> false)))
        && 0 <= length
        && 0 <= pos
        && pos < i₆
        && a₅[pos] == 0
         ==> i₆ < length));

goal (forall b: [int]int, length: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
      (  0 <= length
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= length
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                        i₁ < length
                        && (b[i₁] == 0
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
                 ==> i₁ < length
                  && (b[i₁] == 0
                     ==> false)))
        && b[i₆] == 0
        && 0 <= length
        && 0 <= pos
        && pos < i₆
         ==> a₅[pos] == b[pos]));

goal (forall b: [int]int, length: int, a: [int]int, a₅: [int]int, i₆: int, pos: int ::
      (  0 <= length
        && 0 <= i₆
        && 0 <= i₆
        && i₆ <= length
        && (forall x₂: int, i₁: int ::
              (  x₂ == i₁
                && 0 <= i₁
                && i₁ < i₆
                 ==> (exists i₁: int ::
                        i₁ < length
                        && (b[i₁] == 0
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
                 ==> i₁ < length
                  && (b[i₁] == 0
                     ==> false)))
        && b[i₆] == 0
        && 0 <= length
        && 0 <= pos
        && pos < i₆
        && a₅[pos] == 0
         ==> false));

