goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && i₈ <= alength
        && (forall m₁₂₉: int, i₁₂₈: int ::
              (  0 <= i₁₂₈
                && i₁₂₈ < i₈
                 ==> a[i₁₂₈] < a[m₁₂₉]
                    && i₁₂₈ < alength
                    && 0 <= i₁₂₈
                    && b₆[i₁₂₈] == a[i₁₂₈]
                  ||   (a[i₁₂₈] < a[m₁₂₉]
                       ==> false)
                    && i₁₂₈ < alength
                    && 0 <= i₁₂₈
                    && b₆[i₁₂₈] == a[m₁₂₉]))
        && (forall i₁₃₀: int ::
                  0 <= i₁₃₀
                  && i₁₃₀ < i₈
                || b₆[i₁₃₀] == b[i₁₃₀])
        && i₈ < alength
        && a[i₈] < a[m₇]
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₂] < a[m₁]
          || b₆[i₈ := a[i₈]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && i₈ <= alength
        && (forall m₂₈₀: int, i₂₇₉: int ::
              (  0 <= i₂₇₉
                && i₂₇₉ < i₈
                 ==> a[i₂₇₉] < a[m₂₈₀]
                    && i₂₇₉ < alength
                    && 0 <= i₂₇₉
                    && b₆[i₂₇₉] == a[i₂₇₉]
                  ||   (a[i₂₇₉] < a[m₂₈₀]
                       ==> false)
                    && i₂₇₉ < alength
                    && 0 <= i₂₇₉
                    && b₆[i₂₇₉] == a[m₂₈₀]))
        && (forall i₂₈₁: int ::
                  0 <= i₂₈₁
                  && i₂₈₁ < i₈
                || b₆[i₂₈₁] == b[i₂₈₁])
        && i₈ < alength
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] < a[m₇]
          || a[i₂] < a[m₁]
          || b₆[i₈ := a[m₇]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && i₈ <= alength
        && (forall m₃₅₁: int, i₃₅₀: int ::
              (  0 <= i₃₅₀
                && i₃₅₀ < i₈
                 ==> a[i₃₅₀] < a[m₃₅₁]
                    && i₃₅₀ < alength
                    && 0 <= i₃₅₀
                    && b₆[i₃₅₀] == a[i₃₅₀]
                  ||   (a[i₃₅₀] < a[m₃₅₁]
                       ==> false)
                    && i₃₅₀ < alength
                    && 0 <= i₃₅₀
                    && b₆[i₃₅₀] == a[m₃₅₁]))
        && (forall i₃₅₂: int ::
                  0 <= i₃₅₂
                  && i₃₅₂ < i₈
                || b₆[i₃₅₂] == b[i₃₅₂])
        && i₈ < alength
        && 0 <= i₂
        && i₂ < i₈ + 1
        && a[i₂] < a[m₁]
         ==> a[i₈] < a[m₇]
          || b₆[i₈ := a[m₇]][i₂] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && i₈ <= alength
        && (forall m₃₇₆: int, i₃₇₅: int ::
              (  0 <= i₃₇₅
                && i₃₇₅ < i₈
                 ==> a[i₃₇₅] < a[m₃₇₆]
                    && i₃₇₅ < alength
                    && 0 <= i₃₇₅
                    && b₆[i₃₇₅] == a[i₃₇₅]
                  ||   (a[i₃₇₅] < a[m₃₇₆]
                       ==> false)
                    && i₃₇₅ < alength
                    && 0 <= i₃₇₅
                    && b₆[i₃₇₅] == a[m₃₇₆]))
        && (forall i₃₇₇: int ::
                  0 <= i₃₇₇
                  && i₃₇₇ < i₈
                || b₆[i₃₇₇] == b[i₃₇₇])
        && i₈ < alength
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] < a[m₇]
          || b₆[i₈ := a[m₇]][i₂] == a[i₂]
          || b₆[i₈ := a[m₇]][i₂] == a[m₁]));

