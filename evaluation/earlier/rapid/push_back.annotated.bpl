goal (forall b: [int]int, blength: int, a: [int]int ::
      (  0 <= blength
        && true
         ==> 0 <= 0
          && 0 == 0
          && 0 <= blength
          && 0 <= 0
          && 0 <= 0
          && 0 <= blength
          && (forall x₃: int ::
                ((exists i₂: int ::
                        x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0)
                   ==> (exists alength₁: int, i₂: int ::
                          i₂ < blength
                          && 0 <= i₂
                          && i₂ == alength₁
                          && alength₁ <= blength
                          && x₃ == i₂
                          && 0 <= i₂
                          && i₂ < 0
                          && a[x₃] == b[i₂])))
          && (forall x₃: int ::
                (!((exists i₂: int ::
                        x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0)
                )
                   ==> a[x₃] == a[x₃]))
          && (forall alength₁: int, i₂: int ::
                (  0 <= i₂
                  && i₂ == alength₁
                  && alength₁ <= blength
                  && alength₁ <= alength₁
                  && i₂ <= i₂
                  && 0 <= alength₁
                  && alength₁ < 0
                  && 0 <= i₂
                  && i₂ < 0
                   ==> i₂ < blength))
          && (forall a₇: [int]int, alength₈: int, i₉: int ::
                (  0 <= i₉
                  && i₉ == alength₈
                  && alength₈ <= blength
                  && 0 <= alength₈
                  && 0 <= i₉
                  && i₉ <= blength
                  && (forall x₃: int ::
                        ((exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₉)
                           ==> (exists alength₁: int, i₂: int ::
                                  i₂ < blength
                                  && 0 <= i₂
                                  && i₂ == alength₁
                                  && alength₁ <= blength
                                  && x₃ == i₂
                                  && 0 <= i₂
                                  && i₂ < i₉
                                  && a₇[x₃] == b[i₂])))
                  && (forall x₃: int ::
                        (!((exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₉)
                        )
                           ==> a₇[x₃] == a[x₃]))
                  && (forall alength₁: int, i₂: int ::
                        (  0 <= i₂
                          && i₂ == alength₁
                          && alength₁ <= blength
                          && alength₁ <= alength₁
                          && i₂ <= i₂
                          && 0 <= alength₁
                          && alength₁ < alength₈
                          && 0 <= i₂
                          && i₂ < i₉
                           ==> i₂ < blength))
                   ==> (i₉ < blength
                       ==> 0 <= i₉ + 1
                        && i₉ + 1 == alength₈ + 1
                        && alength₈ + 1 <= blength
                        && 0 <= alength₈ + 1
                        && 0 <= i₉ + 1
                        && i₉ + 1 <= blength
                        && (forall x₃: int ::
                              ((exists i₂: int ::
                                      x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₉ + 1)
                                 ==> (exists alength₁: int, i₂: int ::
                                        i₂ < blength
                                        && 0 <= i₂
                                        && i₂ == alength₁
                                        && alength₁ <= blength
                                        && x₃ == i₂
                                        && 0 <= i₂
                                        && i₂ < i₉ + 1
                                        && a₇[i₉ := b[i₉]][x₃] == b[i₂])))
                        && (forall x₃: int ::
                              (!((exists i₂: int ::
                                      x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₉ + 1)
                              )
                                 ==> a₇[i₉ := b[i₉]][x₃] == a[x₃]))
                        && (forall alength₁: int, i₂: int ::
                              (  0 <= i₂
                                && i₂ == alength₁
                                && alength₁ <= blength
                                && alength₁ <= alength₁
                                && i₂ <= i₂
                                && 0 <= alength₁
                                && alength₁ < alength₈ + 1
                                && 0 <= i₂
                                && i₂ < i₉ + 1
                                 ==> i₂ < blength))
                        && true
                        && (true
                           ==> true))
                    && (!(i₉ < blength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall j: int ::
                                  (  0 <= blength
                                    && 0 <= j
                                    && j < alength₈
                                     ==> a₇[j] == b[j]))))))));

