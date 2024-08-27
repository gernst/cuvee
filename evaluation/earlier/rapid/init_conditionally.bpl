goal (forall a: [int]int, b: [int]int, length: int, c: [int]int ::
      (0 <= length
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= 0
          && 0 <= length
          && (forall x₃: int, clength₁: int ::
                (  x₃ == clength₁
                  && 0 <= clength₁
                  && clength₁ < 0
                   ==> (exists clength₁: int, i₂: int ::
                          a[i₂] == b[i₂]
                          && i₂ < length
                          && 0 <= i₂
                          && x₃ == clength₁
                          && 0 <= clength₁
                          && clength₁ < 0
                          && i₂ < 0
                          && c[x₃] == i₂)))
          && (forall x₃: int ::
                  (exists clength₁: int ::
                          x₃ == clength₁
                          && 0 <= clength₁
                          && clength₁ < 0)
                  || c[x₃] == c[x₃])
          && (forall clength₁: int, i₂: int ::
                (  0 <= i₂
                  && 0 <= clength₁
                  && clength₁ < 0
                  && i₂ < 0
                   ==> i₂ < length))
          && (forall c₇: [int]int, clength₈: int, i₉: int ::
                (  0 <= i₉
                  && 0 <= clength₈
                  && 0 <= i₉
                  && i₉ <= length
                  && (forall x₃: int, clength₁: int ::
                        (  x₃ == clength₁
                          && 0 <= clength₁
                          && clength₁ < clength₈
                           ==> (exists clength₁: int, i₂: int ::
                                  a[i₂] == b[i₂]
                                  && i₂ < length
                                  && 0 <= i₂
                                  && x₃ == clength₁
                                  && 0 <= clength₁
                                  && clength₁ < clength₈
                                  && i₂ < i₉
                                  && c₇[x₃] == i₂)))
                  && (forall x₃: int ::
                          (exists clength₁: int ::
                                  x₃ == clength₁
                                  && 0 <= clength₁
                                  && clength₁ < clength₈)
                          || c₇[x₃] == c[x₃])
                  && (forall clength₁: int, i₂: int ::
                        (  0 <= i₂
                          && 0 <= clength₁
                          && clength₁ < clength₈
                          && i₂ < i₉
                           ==> i₂ < length))
                   ==> (i₉ < length
                       ==> (a[i₉] == b[i₉]
                           ==> 0 <= i₉ + 1
                            && 0 <= clength₈ + 1
                            && 0 <= i₉ + 1
                            && i₉ + 1 <= length
                            && (forall x₃: int, clength₁: int ::
                                  (  x₃ == clength₁
                                    && 0 <= clength₁
                                    && clength₁ < clength₈ + 1
                                     ==> (exists clength₁: int, i₂: int ::
                                            a[i₂] == b[i₂]
                                            && i₂ < length
                                            && 0 <= i₂
                                            && x₃ == clength₁
                                            && 0 <= clength₁
                                            && clength₁ < clength₈ + 1
                                            && i₂ < i₉ + 1
                                            && c₇[clength₈ := i₉][x₃] == i₂)))
                            && (forall x₃: int ::
                                    (exists clength₁: int ::
                                            x₃ == clength₁
                                            && 0 <= clength₁
                                            && clength₁ < clength₈ + 1)
                                    || c₇[clength₈ := i₉][x₃] == c[x₃])
                            && (forall clength₁: int, i₂: int ::
                                  (  0 <= i₂
                                    && 0 <= clength₁
                                    && clength₁ < clength₈ + 1
                                    && i₂ < i₉ + 1
                                     ==> i₂ < length)))
                        &&   a[i₉] == b[i₉]
                          ||   0 <= i₉ + 1
                            && 0 <= clength₈
                            && 0 <= i₉ + 1
                            && i₉ + 1 <= length
                            && (forall x₃: int, clength₁: int ::
                                  (  x₃ == clength₁
                                    && 0 <= clength₁
                                    && clength₁ < clength₈
                                     ==> (exists clength₁: int, i₂: int ::
                                            a[i₂] == b[i₂]
                                            && i₂ < length
                                            && 0 <= i₂
                                            && x₃ == clength₁
                                            && 0 <= clength₁
                                            && clength₁ < clength₈
                                            && i₂ < i₉ + 1
                                            && c₇[x₃] == i₂)))
                            && (forall x₃: int ::
                                    (exists clength₁: int ::
                                            x₃ == clength₁
                                            && 0 <= clength₁
                                            && clength₁ < clength₈)
                                    || c₇[x₃] == c[x₃])
                            && (forall clength₁: int, i₂: int ::
                                  (  0 <= i₂
                                    && 0 <= clength₁
                                    && clength₁ < clength₈
                                    && i₂ < i₉ + 1
                                     ==> i₂ < length)))
                    &&   i₉ < length
                      ||   (forall pos: int ::
                              (  0 <= pos
                                && pos < clength₈
                                && 0 <= length
                                 ==> a[c₇[pos]] == b[c₇[pos]]))
                        && (forall pos: int ::
                              (  0 <= pos
                                && pos < clength₈
                                && 0 <= length
                                 ==> pos <= c₇[pos]))))));

