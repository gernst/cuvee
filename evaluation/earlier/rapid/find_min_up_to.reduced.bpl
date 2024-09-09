goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && (forall m₄₂: int, i₄₁: int ::
              (  0 <= i₄₁
                && i₄₁ < i₈
                 ==> a[i₄₁] < a[m₄₂]
                    && i₄₁ < alength
                    && b₆[i₄₁] == a[i₄₁]
                  ||   (a[i₄₁] < a[m₄₂]
                       ==> false)
                    && i₄₁ < alength
                    && b₆[i₄₁] == a[m₄₂]))
        && (forall i₄₃: int ::
                  0 <= i₄₃
                  && i₄₃ < i₈
                || b₆[i₄₃] == b[i₄₃])
        && i₈ < alength
        && a[i₈] < a[m₇]
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₂] < a[m₁]
            && i₂ < alength
            && b₆[i₈ := a[i₈]][i₂] == a[i₂]
          || b₆[i₈ := a[i₈]][i₂] == a[m₁]));

goal {:named "invariant forward"} (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && (forall m₇₃: int, i₇₂: int ::
              (  0 <= i₇₂
                && i₇₂ < i₈
                 ==> a[i₇₂] < a[m₇₃]
                    && i₇₂ < alength
                    && b₆[i₇₂] == a[i₇₂]
                  ||   (a[i₇₂] < a[m₇₃]
                       ==> false)
                    && i₇₂ < alength
                    && b₆[i₇₂] == a[m₇₃]))
        && (forall i₇₄: int ::
                  0 <= i₇₄
                  && i₇₄ < i₈
                || b₆[i₇₄] == b[i₇₄])
        && i₈ < alength
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] < a[m₇]
          ||   a[i₂] < a[m₁]
            && i₂ < alength
            && b₆[i₈ := a[m₇]][i₂] == a[i₂]
          ||   (a[i₂] < a[m₁]
               ==> false)
            && i₂ < alength
            && b₆[i₈ := a[m₇]][i₂] == a[m₁]));

goal {:named "ensures"} (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, i₈: int, j: int ::
      (  0 <= alength
        && 0 <= i₈
        && (forall m₁: int, i₂: int ::
              (  0 <= i₂
                && i₂ < i₈
                 ==> a[i₂] < a[m₁]
                    && i₂ < alength
                    && b₆[i₂] == a[i₂]
                  ||   (a[i₂] < a[m₁]
                       ==> false)
                    && i₂ < alength
                    && b₆[i₂] == a[m₁]))
        && (forall i₂: int ::
                  0 <= i₂
                  && i₂ < i₈
                || b₆[i₂] == b[i₂])
        && 0 <= alength
         ==> i₈ < alength
          || (exists k: int ::
                (  0 <= j
                  && j < alength
                   ==> 0 <= k
                    && k < j
                    && b₆[j] == a[k]))));

