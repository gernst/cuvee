goal (forall b: [int]int, blength: int, a: [int]int, a₄: [int]int, i₅: int, pos: int ::
      (  0 <= blength
        && 0 <= i₅
        && 0 <= i₅
        && i₅ <= blength
        && (forall i₁: int ::
              (  0 <= i₁
                && i₁ < i₅
                 ==> b[i₁] >= 0
                    && i₁ < blength
                    && 0 <= i₁
                    && a₄[i₁] == b[i₁]
                  ||   (b[i₁] >= 0
                       ==> false)
                    && i₁ < blength
                    && 0 <= i₁
                    && a₄[i₁] == 0))
        && (forall i₁: int ::
                  0 <= i₁
                  && i₁ < i₅
                || a₄[i₁] == a[i₁])
        && 0 <= pos
        && pos < blength
        && 0 <= blength
         ==> i₅ < blength
          || a₄[pos] <= 0));

