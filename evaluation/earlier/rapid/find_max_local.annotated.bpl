goal (forall a: [int]int, alength: int, b: [int]int ::
      (  1 <= alength
        && true
        && true
        && true
         ==> 0 <= 1
          && 1 <= 1
          && 1 <= 1
          && 1 <= alength
          && (forall x₄: int ::
                ((exists i₃: int ::
                        x₄ == i₃
                        && 1 <= i₃
                        && i₃ < 1)
                   ==> (exists m₂: int, i₃: int ::
                          a[i₃] > a[m₂]
                          && i₃ < alength
                          && 0 <= i₃
                          && x₄ == i₃
                          && 1 <= i₃
                          && i₃ < 1
                          && b[0 := a[0]][x₄] == a[i₃])))
          && (forall x₄: int ::
                (!((exists i₃: int ::
                        x₄ == i₃
                        && 1 <= i₃
                        && i₃ < 1)
                )
                   ==> b[0 := a[0]][x₄] == b[0 := a[0]][x₄]))
          && (forall blength₁: int, i₃: int ::
                (  0 <= i₃
                  && blength₁ <= blength₁
                  && i₃ <= i₃
                  && 1 <= blength₁
                  && blength₁ < 1
                  && 1 <= i₃
                  && i₃ < 1
                   ==> i₃ < alength))
          && (forall b₉: [int]int, blength₁₀: int, m₁₁: int, i₁₂: int ::
                (  0 <= i₁₂
                  && 1 <= blength₁₀
                  && 1 <= i₁₂
                  && i₁₂ <= alength
                  && (forall x₄: int ::
                        ((exists i₃: int ::
                                x₄ == i₃
                                && 1 <= i₃
                                && i₃ < i₁₂)
                           ==> (exists m₂: int, i₃: int ::
                                  a[i₃] > a[m₂]
                                  && i₃ < alength
                                  && 0 <= i₃
                                  && x₄ == i₃
                                  && 1 <= i₃
                                  && i₃ < i₁₂
                                  && b₉[x₄] == a[i₃])))
                  && (forall x₄: int ::
                        (!((exists i₃: int ::
                                x₄ == i₃
                                && 1 <= i₃
                                && i₃ < i₁₂)
                        )
                           ==> b₉[x₄] == b[0 := a[0]][x₄]))
                  && (forall blength₁: int, i₃: int ::
                        (  0 <= i₃
                          && blength₁ <= blength₁
                          && i₃ <= i₃
                          && 1 <= blength₁
                          && blength₁ < blength₁₀
                          && 1 <= i₃
                          && i₃ < i₁₂
                           ==> i₃ < alength))
                   ==> (i₁₂ < alength
                       ==> (a[i₁₂] > a[m₁₁]
                           ==> 0 <= i₁₂ + 1
                            && 1 <= blength₁₀ + 1
                            && 1 <= i₁₂ + 1
                            && i₁₂ + 1 <= alength
                            && (forall x₄: int ::
                                  ((exists i₃: int ::
                                          x₄ == i₃
                                          && 1 <= i₃
                                          && i₃ < i₁₂ + 1)
                                     ==> (exists m₂: int, i₃: int ::
                                            a[i₃] > a[m₂]
                                            && i₃ < alength
                                            && 0 <= i₃
                                            && x₄ == i₃
                                            && 1 <= i₃
                                            && i₃ < i₁₂ + 1
                                            && b₉[i₁₂ := a[i₁₂]][x₄] == a[i₃])))
                            && (forall x₄: int ::
                                  (!((exists i₃: int ::
                                          x₄ == i₃
                                          && 1 <= i₃
                                          && i₃ < i₁₂ + 1)
                                  )
                                     ==> b₉[i₁₂ := a[i₁₂]][x₄] == b[0 := a[0]][x₄]))
                            && (forall blength₁: int, i₃: int ::
                                  (  0 <= i₃
                                    && blength₁ <= blength₁
                                    && i₃ <= i₃
                                    && 1 <= blength₁
                                    && blength₁ < blength₁₀ + 1
                                    && 1 <= i₃
                                    && i₃ < i₁₂ + 1
                                     ==> i₃ < alength))
                            && true
                            && (true
                               ==> true))
                        && (!(a[i₁₂] > a[m₁₁]
                        )
                           ==> 0 <= i₁₂ + 1
                            && 1 <= blength₁₀
                            && 1 <= i₁₂ + 1
                            && i₁₂ + 1 <= alength
                            && (forall x₄: int ::
                                  ((exists i₃: int ::
                                          x₄ == i₃
                                          && 1 <= i₃
                                          && i₃ < i₁₂ + 1)
                                     ==> (exists m₂: int, i₃: int ::
                                            a[i₃] > a[m₂]
                                            && i₃ < alength
                                            && 0 <= i₃
                                            && x₄ == i₃
                                            && 1 <= i₃
                                            && i₃ < i₁₂ + 1
                                            && b₉[x₄] == a[i₃])))
                            && (forall x₄: int ::
                                  (!((exists i₃: int ::
                                          x₄ == i₃
                                          && 1 <= i₃
                                          && i₃ < i₁₂ + 1)
                                  )
                                     ==> b₉[x₄] == b[0 := a[0]][x₄]))
                            && (forall blength₁: int, i₃: int ::
                                  (  0 <= i₃
                                    && blength₁ <= blength₁
                                    && i₃ <= i₃
                                    && 1 <= blength₁
                                    && blength₁ < blength₁₀
                                    && 1 <= i₃
                                    && i₃ < i₁₂ + 1
                                     ==> i₃ < alength))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₁₂ < alength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall k: int ::
                                  (  1 <= alength
                                    && 0 <= k
                                    && k < alength
                                    && (forall l: int ::
                                          (  0 <= l
                                            && l < k
                                             ==> a[l] < a[k]))
                                     ==> (exists j: int ::
                                            0 <= j
                                            && j < blength₁₀
                                            && a[k] == b₉[j])))
                            && (forall j: int ::
                                  (exists k: int ::
                                        (  1 <= alength
                                          && 0 <= j
                                          && j < blength₁₀
                                           ==> 0 <= k
                                            && k < alength
                                            && b₉[j] == a[k])))
                            && (forall j: int, k: int ::
                                  (  1 <= alength
                                    && 0 <= j
                                    && 0 <= k
                                    && j <= k
                                    && k < blength₁₀
                                     ==> b₉[j] <= b₉[k]))))))));

