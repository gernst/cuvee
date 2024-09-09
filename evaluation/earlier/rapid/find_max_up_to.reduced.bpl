goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₁₂₂: int, i₁₂₁: int ::
              (  0 <= i₁₂₁
                && 0 <= i₁₂₁
                && i₁₂₁ < i₈
                 ==> a[i₁₂₁] > a[m₁₂₂]
                    && i₁₂₁ < alength
                    && 0 <= i₁₂₁
                    && b₆[i₁₂₁] == a[i₁₂₁]
                  ||   (a[i₁₂₁] > a[m₁₂₂]
                       ==> false)
                    && i₁₂₁ < alength
                    && 0 <= i₁₂₁
                    && b₆[i₁₂₁] == a[m₁₂₂]))
        && (forall i₁₂₃: int ::
              (0 <= i₁₂₃
                 ==> 0 <= i₁₂₃
                    && i₁₂₃ < i₈
                  || b₆[i₁₂₃] == b[i₁₂₃]))
        && i₈ < alength
        && a[i₈] > a[m₇]
        && 0 <= i₂
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₂] > a[m₁]
          || b₆[i₈ := a[i₈]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₂₆₇: int, i₂₆₆: int ::
              (  0 <= i₂₆₆
                && 0 <= i₂₆₆
                && i₂₆₆ < i₈
                 ==> a[i₂₆₆] > a[m₂₆₇]
                    && i₂₆₆ < alength
                    && 0 <= i₂₆₆
                    && b₆[i₂₆₆] == a[i₂₆₆]
                  ||   (a[i₂₆₆] > a[m₂₆₇]
                       ==> false)
                    && i₂₆₆ < alength
                    && 0 <= i₂₆₆
                    && b₆[i₂₆₆] == a[m₂₆₇]))
        && (forall i₂₆₈: int ::
              (0 <= i₂₆₈
                 ==> 0 <= i₂₆₈
                    && i₂₆₈ < i₈
                  || b₆[i₂₆₈] == b[i₂₆₈]))
        && i₈ < alength
        && 0 <= i₂
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] > a[m₇]
          || a[i₂] > a[m₁]
          || b₆[i₈ := a[m₇]][i₂] == a[m₁]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₃₃₈: int, i₃₃₇: int ::
              (  0 <= i₃₃₇
                && 0 <= i₃₃₇
                && i₃₃₇ < i₈
                 ==> a[i₃₃₇] > a[m₃₃₈]
                    && i₃₃₇ < alength
                    && 0 <= i₃₃₇
                    && b₆[i₃₃₇] == a[i₃₃₇]
                  ||   (a[i₃₃₇] > a[m₃₃₈]
                       ==> false)
                    && i₃₃₇ < alength
                    && 0 <= i₃₃₇
                    && b₆[i₃₃₇] == a[m₃₃₈]))
        && (forall i₃₃₉: int ::
              (0 <= i₃₃₉
                 ==> 0 <= i₃₃₉
                    && i₃₃₉ < i₈
                  || b₆[i₃₃₉] == b[i₃₃₉]))
        && i₈ < alength
        && 0 <= i₂
        && 0 <= i₂
        && i₂ < i₈ + 1
        && a[i₂] > a[m₁]
         ==> a[i₈] > a[m₇]
          || b₆[i₈ := a[m₇]][i₂] == a[i₂]));

goal (forall a: [int]int, alength: int, b: [int]int, b₆: [int]int, m₇: int, i₈: int, m₁: int, i₂: int ::
      (  0 <= alength
        && 0 <= i₈
        && 0 <= i₈
        && (forall m₃₆₃: int, i₃₆₂: int ::
              (  0 <= i₃₆₂
                && 0 <= i₃₆₂
                && i₃₆₂ < i₈
                 ==> a[i₃₆₂] > a[m₃₆₃]
                    && i₃₆₂ < alength
                    && 0 <= i₃₆₂
                    && b₆[i₃₆₂] == a[i₃₆₂]
                  ||   (a[i₃₆₂] > a[m₃₆₃]
                       ==> false)
                    && i₃₆₂ < alength
                    && 0 <= i₃₆₂
                    && b₆[i₃₆₂] == a[m₃₆₃]))
        && (forall i₃₆₄: int ::
              (0 <= i₃₆₄
                 ==> 0 <= i₃₆₄
                    && i₃₆₄ < i₈
                  || b₆[i₃₆₄] == b[i₃₆₄]))
        && i₈ < alength
        && 0 <= i₂
        && 0 <= i₂
        && i₂ < i₈ + 1
         ==> a[i₈] > a[m₇]
          || b₆[i₈ := a[m₇]][i₂] == a[i₂]
          || b₆[i₈ := a[m₇]][i₂] == a[m₁]));

