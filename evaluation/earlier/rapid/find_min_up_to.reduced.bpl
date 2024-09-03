goal (forall a: [int]int, alength: int, b: [int]int, b₇: [int]int, i₉: int, j: int, k: int ::
      (  0 <= alength
        && 0 <= i₉
        && 0 <= i₉
        && i₉ <= alength
        && (forall x₃: int, i₂: int ::
              (  x₃ == i₂
                && 0 <= i₂
                && i₂ < i₉
                 ==> (exists m₁: int, i₂: int ::
                          a[i₂] < a[m₁]
                          && i₂ < alength
                          && 0 <= i₂
                          && x₃ == i₂
                          && 0 <= i₂
                          && i₂ < i₉
                          && b₇[x₃] == a[i₂])
                  || (exists m₁: int, i₂: int ::
                        (a[i₂] < a[m₁]
                           ==> false))))
        && (forall x₃: int ::
                (exists i₂: int ::
                        x₃ == i₂
                        && 0 <= i₂
                        && i₂ < i₉)
                || b₇[x₃] == b[x₃])
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ <= i₂
                && 0 <= i₂
                && i₂ < i₉
                 ==> i₂ < alength))
        && 0 <= alength
        && 0 <= j
        && 0 <= k
        && k <= j
        && j < alength
         ==> i₉ < alength
          || b₇[j] <= b₇[k]));

