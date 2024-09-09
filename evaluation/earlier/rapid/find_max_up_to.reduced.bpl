goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && (forall m₉₁: int, i₉₀: int ::
              (  0 <= i₉₀
                && i₉₀ < i₈
                 ==> a[i₉₀] > a[m₉₁]
                    && i₉₀ < alength
                    && b₆[i₉₀] == a[i₉₀]
                  ||   (a[i₉₀] > a[m₉₁]
                       ==> false)
                    && i₉₀ < alength
                    && b₆[i₉₀] == a[m₉₁]))
        && (forall i₉₂: int ::
                  0 <= i₉₂
                  && i₉₂ < i₈
                || b₆[i₉₂] == b[i₉₂])
        && i₈ < alength
        && a[i₈] > a[m₇]
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₂] > a[m₁]
          || b₆[i₈ := a[i₈]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && (forall m₁₈₄: int, i₁₈₃: int ::
              (  0 <= i₁₈₃
                && i₁₈₃ < i₈
                 ==> a[i₁₈₃] > a[m₁₈₄]
                    && i₁₈₃ < alength
                    && b₆[i₁₈₃] == a[i₁₈₃]
                  ||   (a[i₁₈₃] > a[m₁₈₄]
                       ==> false)
                    && i₁₈₃ < alength
                    && b₆[i₁₈₃] == a[m₁₈₄]))
        && (forall i₁₈₅: int ::
                  0 <= i₁₈₅
                  && i₁₈₅ < i₈
                || b₆[i₁₈₅] == b[i₁₈₅])
        && i₈ < alength
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] > a[m₇]
          || a[i₂] > a[m₁]
          || b₆[i₈ := a[m₇]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && (forall m₂₁₈: int, i₂₁₇: int ::
              (  0 <= i₂₁₇
                && i₂₁₇ < i₈
                 ==> a[i₂₁₇] > a[m₂₁₈]
                    && i₂₁₇ < alength
                    && b₆[i₂₁₇] == a[i₂₁₇]
                  ||   (a[i₂₁₇] > a[m₂₁₈]
                       ==> false)
                    && i₂₁₇ < alength
                    && b₆[i₂₁₇] == a[m₂₁₈]))
        && (forall i₂₁₉: int ::
                  0 <= i₂₁₉
                  && i₂₁₉ < i₈
                || b₆[i₂₁₉] == b[i₂₁₉])
        && i₈ < alength
        && 0 <= i₂
        && i₂ < i₈ + 1
        && a[i₂] > a[m₁]
         ==> a[i₈] > a[m₇]
          || b₆[i₈ := a[m₇]][i₂] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && (forall m₂₃₆: int, i₂₃₅: int ::
              (  0 <= i₂₃₅
                && i₂₃₅ < i₈
                 ==> a[i₂₃₅] > a[m₂₃₆]
                    && i₂₃₅ < alength
                    && b₆[i₂₃₅] == a[i₂₃₅]
                  ||   (a[i₂₃₅] > a[m₂₃₆]
                       ==> false)
                    && i₂₃₅ < alength
                    && b₆[i₂₃₅] == a[m₂₃₆]))
        && (forall i₂₃₇: int ::
                  0 <= i₂₃₇
                  && i₂₃₇ < i₈
                || b₆[i₂₃₇] == b[i₂₃₇])
        && i₈ < alength
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] > a[m₇]
          || b₆[i₈ := a[m₇]][i₂] == a[i₂]
          || b₆[i₈ := a[m₇]][i₂] == a[m₁]));

