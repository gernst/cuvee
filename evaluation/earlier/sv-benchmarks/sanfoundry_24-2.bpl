data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall i: int ::
      i % 2 == 0);

goal (forall i: int ::
      (i % 2 == 0
         ==> false));

goal (forall array: [int]int, __VERIFIER_nondet_int₁: int ::
        0 <= 0
        && 0 <= __VERIFIER_nondet_int₁
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < 0
                 ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                        i₆ < __VERIFIER_nondet_int₁
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < 0
                        && array[x₇] == __VERIFIER_nondet_int₂₅)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < 0)
                || array[x₇] == array[x₇])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < 0
                 ==> i₆ < __VERIFIER_nondet_int₁))
        && (forall array₁₈: [int]int, i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ <= __VERIFIER_nondet_int₁
                && (forall x₇: int, i₆: int ::
                      (  x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₁₉
                         ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                i₆ < __VERIFIER_nondet_int₁
                                && x₇ == i₆
                                && 0 <= i₆
                                && i₆ < i₁₉
                                && array₁₈[x₇] == __VERIFIER_nondet_int₂₅)))
                && (forall x₇: int ::
                        (exists i₆: int ::
                                x₇ == i₆
                                && 0 <= i₆
                                && i₆ < i₁₉)
                        || array₁₈[x₇] == array[x₇])
                && (forall i₆: int ::
                      (  0 <= i₆
                        && i₆ < i₁₉
                         ==> i₆ < __VERIFIER_nondet_int₁))
                 ==> (forall __VERIFIER_nondet_int₂: int ::
                        (i₁₉ < __VERIFIER_nondet_int₁
                           ==> 0 <= i₁₉ + 1
                            && i₁₉ + 1 <= __VERIFIER_nondet_int₁
                            && (forall x₇: int, i₆: int ::
                                  (  x₇ == i₆
                                    && 0 <= i₆
                                    && i₆ < i₁₉ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                            i₆ < __VERIFIER_nondet_int₁
                                            && x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₁₉ + 1
                                            && array₁₈[i₁₉ := __VERIFIER_nondet_int₂][x₇] == __VERIFIER_nondet_int₂₅)))
                            && (forall x₇: int ::
                                    (exists i₆: int ::
                                            x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₁₉ + 1)
                                    || array₁₈[i₁₉ := __VERIFIER_nondet_int₂][x₇] == array[x₇])
                            && (forall i₆: int ::
                                  (  0 <= i₆
                                    && i₆ < i₁₉ + 1
                                     ==> i₆ < __VERIFIER_nondet_int₁))))
                  &&   i₁₉ < __VERIFIER_nondet_int₁
                    ||   0 <= __VERIFIER_nondet_int₁
                      && (forall i₁₂: int ::
                            i₁₂ < __VERIFIER_nondet_int₁)
                      && (forall i₂₀: int ::
                            (  i₂₀ <= __VERIFIER_nondet_int₁
                              && (forall i₁₂: int ::
                                    i₁₂ < __VERIFIER_nondet_int₁)
                               ==> (i₂₀ < __VERIFIER_nondet_int₁
                                   ==> (array₁₈[i₂₀] % 2 == 0
                                       ==> array₁₈[i₂₀] % 2 == 0
                                        && i₂₀ + 1 <= __VERIFIER_nondet_int₁
                                        && (forall i₁₂: int ::
                                              i₁₂ < __VERIFIER_nondet_int₁))
                                    &&   array₁₈[i₂₀] % 2 == 0
                                      ||   i₂₀ + 1 <= __VERIFIER_nondet_int₁
                                        && (forall i₁₂: int ::
                                              i₁₂ < __VERIFIER_nondet_int₁))
                                &&   i₂₀ < __VERIFIER_nondet_int₁
                                  ||   0 <= __VERIFIER_nondet_int₁
                                    && (forall i₁₆: int ::
                                          i₁₆ < __VERIFIER_nondet_int₁)
                                    && (forall i₂₁: int ::
                                          (  i₂₁ <= __VERIFIER_nondet_int₁
                                            && (forall i₁₆: int ::
                                                  i₁₆ < __VERIFIER_nondet_int₁)
                                             ==> (i₂₁ < __VERIFIER_nondet_int₁
                                               ==> array₁₈[i₂₁] % 2 == 0
                                                  || (array₁₈[i₂₁] % 2 == 0
                                                     ==> false)
                                                && (array₁₈[i₂₁] % 2 == 0
                                                   ==> i₂₁ + 1 <= __VERIFIER_nondet_int₁
                                                    && (forall i₁₆: int ::
                                                          i₁₆ < __VERIFIER_nondet_int₁))))))))));

