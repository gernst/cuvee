goal (forall length: int, a: [int]int, b: [int]int, a₅: [int]int, b₆: [int]int, i₇: int, i₁: int ::
      (  0 <= length
        && 0 <= i₇
        && 0 <= i₇
        && (forall i₅₁: int ::
              (  0 <= i₅₁
                && 0 <= i₅₁
                && i₅₁ < i₇
                 ==> i₅₁ < length
                  && 0 <= i₅₁
                  && a₅[i₅₁] == b[i₅₁]
                  && b₆[i₅₁] == a[i₅₁]))
        && i₇ < length
        && 0 <= i₁
        && 0 <= i₁
        && i₁ < i₇ + 1
         ==> a₅[i₇ := b₆[i₇]][i₁] == b[i₁]));

goal (forall length: int, a: [int]int, b: [int]int, a₅: [int]int, b₆: [int]int, i₇: int, i₁: int ::
      (  0 <= length
        && 0 <= i₇
        && 0 <= i₇
        && (forall i₅₉: int ::
              (  0 <= i₅₉
                && 0 <= i₅₉
                && i₅₉ < i₇
                 ==> i₅₉ < length
                  && 0 <= i₅₉
                  && a₅[i₅₉] == b[i₅₉]
                  && b₆[i₅₉] == a[i₅₉]))
        && i₇ < length
        && 0 <= i₁
        && 0 <= i₁
        && i₁ < i₇ + 1
         ==> b₆[i₇ := a₅[i₇]][i₁] == a[i₁]));

