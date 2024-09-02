goal (forall a: [int]int, b: [int]int, alength: int, c: [int]int ::
      (  0 <= alength
        && true
        && true
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= alength
          && (forall x₂: int ::
                ((exists i₁: int ::
                      if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < 0 else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < 0)
                   ==> (exists i₁: int ::
                          i₁ < alength
                          && 0 <= i₁
                          && if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < 0 && c[x₂] == b[i₁] else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < 0 && c[x₂] == a[i₁])))
          && (forall x₂: int ::
                (!((exists i₁: int ::
                      if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < 0 else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < 0)
                )
                   ==> c[x₂] == c[x₂]))
          && (forall i₁: int ::
                (  0 <= i₁
                  && 0 <= i₁
                  && i₁ < 0
                   ==> i₁ < alength))
          && (forall c₅: [int]int, i₆: int ::
                (  0 <= i₆
                  && 0 <= i₆
                  && i₆ <= alength
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                              if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < i₆ else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < i₆)
                           ==> (exists i₁: int ::
                                  i₁ < alength
                                  && 0 <= i₁
                                  && if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < i₆ && c₅[x₂] == b[i₁] else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < i₆ && c₅[x₂] == a[i₁])))
                  && (forall x₂: int ::
                        (!((exists i₁: int ::
                              if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < i₆ else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < i₆)
                        )
                           ==> c₅[x₂] == c[x₂]))
                  && (forall i₁: int ::
                        (  0 <= i₁
                          && 0 <= i₁
                          && i₁ < i₆
                           ==> i₁ < alength))
                   ==> (i₆ < alength
                       ==> 0 <= i₆ + 1
                        && 0 <= i₆ + 1
                        && i₆ + 1 <= alength
                        && (forall x₂: int ::
                              ((exists i₁: int ::
                                    if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < i₆ + 1 else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < i₆ + 1)
                                 ==> (exists i₁: int ::
                                        i₁ < alength
                                        && 0 <= i₁
                                        && if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < i₆ + 1 && c₅[i₆ * 2 := a[i₆]][i₆ * 2 + 1 := b[i₆]][x₂] == b[i₁] else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < i₆ + 1 && c₅[i₆ * 2 := a[i₆]][i₆ * 2 + 1 := b[i₆]][x₂] == a[i₁])))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                    if(x₂ == 1 + 2 * i₁) then 0 <= i₁ && i₁ < i₆ + 1 else x₂ == 2 * i₁ && 0 <= i₁ && i₁ < i₆ + 1)
                              )
                                 ==> c₅[i₆ * 2 := a[i₆]][i₆ * 2 + 1 := b[i₆]][x₂] == c[x₂]))
                        && (forall i₁: int ::
                              (  0 <= i₁
                                && 0 <= i₁
                                && i₁ < i₆ + 1
                                 ==> i₁ < alength))
                        && true
                        && (true
                           ==> true))
                    && (!(i₆ < alength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                     ==> c₅[pos * 2] == a[pos]))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                     ==> c₅[pos * 2 + 1] == b[pos]))
                            && (forall pos: int ::
                                  (exists j: int ::
                                        (  0 <= alength
                                          && 0 <= pos
                                          && pos < alength
                                           ==> c₅[pos] == a[j]
                                            || c₅[pos] == b[j])))))))));

