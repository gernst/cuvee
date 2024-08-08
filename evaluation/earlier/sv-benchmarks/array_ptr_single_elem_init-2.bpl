data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, c: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₈: int, i₇: int, i₄₈: int ::
              (  (x₈ == i₇
                   ==> 0 <= i₇
                    && i₇ < 0)
                &&   x₈ == i₇
                  ||   x₈ == i₇
                    && 0 <= i₇
                    && i₇ < 0
                && x₈ == i₄₈
                && 0 <= i₄₈
                && i₄₈ < 0
                 ==> (exists i₇: int ::
                          b[i₇ := i₇ % 2][i₇] == 0
                          && (a[i₇ := 0][i₇ := 1][i₇] == 0
                             ==> false))
                  || (exists i₇: int ::
                          b[i₇] == 0
                          && (a[i₇ := 0][i₇] == 0
                             ==> false))
                  || (exists i₇: int ::
                        (b[i₇ := i₇ % 2][i₇] == 0
                           ==> false))
                  || (exists i₇: int ::
                        (b[i₇] == 0
                           ==> false))
                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                          a[i₇ := 0][i₇ := 1][i₇] == 0
                          && __VERIFIER_nondet_int₁₅ == 0
                          && i₇ < 100000
                          && if(x₈ == i₇) then 0 <= i₇ && i₇ < 0 && a[x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < 0 && a[x₈] == 0)
                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                          a[i₇ := 0][i₇] == 0
                          && (__VERIFIER_nondet_int₁₅ == 0
                             ==> false))))
        && (forall x₈: int ::
                (exists i₇: int, i₄₉: int ::
                        if(x₈ == i₇) then 0 <= i₇ && i₇ < 0 else x₈ == i₇ && 0 <= i₇ && i₇ < 0
                        && x₈ == i₄₉
                        && 0 <= i₄₉
                        && i₄₉ < 0)
                || a[x₈] == a[x₈])
        && (forall x₉: int, i₇: int ::
              (  x₉ == i₇
                && 0 <= i₇
                && i₇ < 0
                 ==> (exists i₇: int ::
                          b[i₇ := i₇ % 2][i₇] == 0
                          && (a[i₇ := 0][i₇ := 1][i₇] == 0
                             ==> false))
                  || (exists i₇: int ::
                        (b[i₇ := i₇ % 2][i₇] == 0
                           ==> false))
                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                          a[i₇ := 0][i₇ := 1][i₇] == 0
                          && __VERIFIER_nondet_int₁₅ == 0
                          && i₇ < 100000
                          && x₉ == i₇
                          && 0 <= i₇
                          && i₇ < 0
                          && b[x₉] == i₇ % 2)))
        && (forall x₉: int ::
                (exists i₇: int ::
                        x₉ == i₇
                        && 0 <= i₇
                        && i₇ < 0)
                || b[x₉] == b[x₉])
        && (forall x₁₀: int, i₇: int ::
              (  x₁₀ == i₇
                && 0 <= i₇
                && i₇ < 0
                 ==> (exists i₇: int ::
                          b[i₇ := i₇ % 2][i₇] == 0
                          && (a[i₇ := 0][i₇ := 1][i₇] == 0
                             ==> false))
                  || (exists i₇: int ::
                          b[i₇] == 0
                          && (a[i₇ := 0][i₇] == 0
                             ==> false))
                  || (exists i₇: int ::
                        (b[i₇ := i₇ % 2][i₇] == 0
                           ==> false))
                  || (exists i₇: int ::
                        (b[i₇] == 0
                           ==> false))))
        && (forall x₁₀: int ::
                (exists i₇: int ::
                        x₁₀ == i₇
                        && 0 <= i₇
                        && i₇ < 0)
                || c[x₁₀] == c[x₁₀])
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < 0
                 ==> i₇ < 100000))
        && (forall i₁₇: int, a₁₈: [int]int, b₁₉: [int]int, c₂₀: [int]int ::
              (  0 <= i₁₇
                && i₁₇ <= 100000
                && (forall x₈: int, i₇: int, i₅₀: int ::
                      (  (x₈ == i₇
                           ==> 0 <= i₇
                            && i₇ < i₁₇)
                        &&   x₈ == i₇
                          ||   x₈ == i₇
                            && 0 <= i₇
                            && i₇ < i₁₇
                        && x₈ == i₅₀
                        && 0 <= i₅₀
                        && i₅₀ < i₁₇
                         ==> (exists i₇: int ::
                                  b₁₉[i₇ := i₇ % 2][i₇] == 0
                                  && (a₁₈[i₇ := 0][i₇ := 1][i₇] == 0
                                     ==> false))
                          || (exists i₇: int ::
                                  b₁₉[i₇] == 0
                                  && (a₁₈[i₇ := 0][i₇] == 0
                                     ==> false))
                          || (exists i₇: int ::
                                (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                   ==> false))
                          || (exists i₇: int ::
                                (b₁₉[i₇] == 0
                                   ==> false))
                          || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                  a₁₈[i₇ := 0][i₇ := 1][i₇] == 0
                                  && __VERIFIER_nondet_int₁₅ == 0
                                  && i₇ < 100000
                                  && if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ && a₁₈[x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ && a₁₈[x₈] == 0)
                          || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                  a₁₈[i₇ := 0][i₇] == 0
                                  && (__VERIFIER_nondet_int₁₅ == 0
                                     ==> false))))
                && (forall x₈: int ::
                        (exists i₇: int, i₅₁: int ::
                                if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇
                                && x₈ == i₅₁
                                && 0 <= i₅₁
                                && i₅₁ < i₁₇)
                        || a₁₈[x₈] == a[x₈])
                && (forall x₉: int, i₇: int ::
                      (  x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i₁₇
                         ==> (exists i₇: int ::
                                  b₁₉[i₇ := i₇ % 2][i₇] == 0
                                  && (a₁₈[i₇ := 0][i₇ := 1][i₇] == 0
                                     ==> false))
                          || (exists i₇: int ::
                                (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                   ==> false))
                          || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                  a₁₈[i₇ := 0][i₇ := 1][i₇] == 0
                                  && __VERIFIER_nondet_int₁₅ == 0
                                  && i₇ < 100000
                                  && x₉ == i₇
                                  && 0 <= i₇
                                  && i₇ < i₁₇
                                  && b₁₉[x₉] == i₇ % 2)))
                && (forall x₉: int ::
                        (exists i₇: int ::
                                x₉ == i₇
                                && 0 <= i₇
                                && i₇ < i₁₇)
                        || b₁₉[x₉] == b[x₉])
                && (forall x₁₀: int, i₇: int ::
                      (  x₁₀ == i₇
                        && 0 <= i₇
                        && i₇ < i₁₇
                         ==> (exists i₇: int ::
                                  b₁₉[i₇ := i₇ % 2][i₇] == 0
                                  && (a₁₈[i₇ := 0][i₇ := 1][i₇] == 0
                                     ==> false))
                          || (exists i₇: int ::
                                  b₁₉[i₇] == 0
                                  && (a₁₈[i₇ := 0][i₇] == 0
                                     ==> false))
                          || (exists i₇: int ::
                                (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                   ==> false))
                          || (exists i₇: int ::
                                (b₁₉[i₇] == 0
                                   ==> false))))
                && (forall x₁₀: int ::
                        (exists i₇: int ::
                                x₁₀ == i₇
                                && 0 <= i₇
                                && i₇ < i₁₇)
                        || c₂₀[x₁₀] == c[x₁₀])
                && (forall i₇: int ::
                      (  0 <= i₇
                        && i₇ < i₁₇
                         ==> i₇ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₁₇ < 100000
                           ==> (__VERIFIER_nondet_int₁ == 0
                               ==> a₁₈[i₁₇ := 0][i₁₇ := 1][i₁₇] == 0
                                  ||   (b₁₉[i₁₇ := i₁₇ % 2][i₁₇] == 0
                                       ==> 0 <= i₁₇ + 1
                                        && i₁₇ + 1 <= 100000
                                        && (forall x₈: int, i₇: int, i₅₂: int ::
                                              (  (x₈ == i₇
                                                   ==> 0 <= i₇
                                                    && i₇ < i₁₇ + 1)
                                                &&   x₈ == i₇
                                                  ||   x₈ == i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₇ + 1
                                                && x₈ == i₅₂
                                                && 0 <= i₅₂
                                                && i₅₂ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                          && __VERIFIER_nondet_int₁₅ == 0
                                                          && i₇ < 100000
                                                          && if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == 0)
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                          && (__VERIFIER_nondet_int₁₅ == 0
                                                             ==> false))))
                                        && (forall x₈: int ::
                                                (exists i₇: int, i₅₃: int ::
                                                        if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1
                                                        && x₈ == i₅₃
                                                        && 0 <= i₅₃
                                                        && i₅₃ < i₁₇ + 1)
                                                || a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == a[x₈])
                                        && (forall x₉: int, i₇: int ::
                                              (  x₉ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                          && __VERIFIER_nondet_int₁₅ == 0
                                                          && i₇ < 100000
                                                          && x₉ == i₇
                                                          && 0 <= i₇
                                                          && i₇ < i₁₇ + 1
                                                          && b₁₉[i₁₇ := i₁₇ % 2][x₉] == i₇ % 2)))
                                        && (forall x₉: int ::
                                                (exists i₇: int ::
                                                        x₉ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇ + 1)
                                                || b₁₉[i₁₇ := i₁₇ % 2][x₉] == b[x₉])
                                        && (forall x₁₀: int, i₇: int ::
                                              (  x₁₀ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                           ==> false))))
                                        && (forall x₁₀: int ::
                                                (exists i₇: int ::
                                                        x₁₀ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇ + 1)
                                                || c₂₀[i₁₇ := 0][x₁₀] == c[x₁₀])
                                        && (forall i₇: int ::
                                              (  0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> i₇ < 100000)))
                                    &&   b₁₉[i₁₇ := i₁₇ % 2][i₁₇] == 0
                                      ||   0 <= i₁₇ + 1
                                        && i₁₇ + 1 <= 100000
                                        && (forall x₈: int, i₇: int, i₅₄: int ::
                                              (  (x₈ == i₇
                                                   ==> 0 <= i₇
                                                    && i₇ < i₁₇ + 1)
                                                &&   x₈ == i₇
                                                  ||   x₈ == i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₇ + 1
                                                && x₈ == i₅₄
                                                && 0 <= i₅₄
                                                && i₅₄ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                          && __VERIFIER_nondet_int₁₅ == 0
                                                          && i₇ < 100000
                                                          && if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == 0)
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                          && (__VERIFIER_nondet_int₁₅ == 0
                                                             ==> false))))
                                        && (forall x₈: int ::
                                                (exists i₇: int, i₅₅: int ::
                                                        if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1
                                                        && x₈ == i₅₅
                                                        && 0 <= i₅₅
                                                        && i₅₅ < i₁₇ + 1)
                                                || a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == a[x₈])
                                        && (forall x₉: int, i₇: int ::
                                              (  x₉ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                          && __VERIFIER_nondet_int₁₅ == 0
                                                          && i₇ < 100000
                                                          && x₉ == i₇
                                                          && 0 <= i₇
                                                          && i₇ < i₁₇ + 1
                                                          && b₁₉[i₁₇ := i₁₇ % 2][x₉] == i₇ % 2)))
                                        && (forall x₉: int ::
                                                (exists i₇: int ::
                                                        x₉ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇ + 1)
                                                || b₁₉[i₁₇ := i₁₇ % 2][x₉] == b[x₉])
                                        && (forall x₁₀: int, i₇: int ::
                                              (  x₁₀ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                          b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                           ==> false))))
                                        && (forall x₁₀: int ::
                                                (exists i₇: int ::
                                                        x₁₀ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇ + 1)
                                                || c₂₀[i₁₇ := 1][x₁₀] == c[x₁₀])
                                        && (forall i₇: int ::
                                              (  0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> i₇ < 100000))
                                && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₁₇] == 0
                                   ==> 0 <= i₁₇ + 1
                                    && i₁₇ + 1 <= 100000
                                    && (forall x₈: int, i₇: int, i₅₆: int ::
                                          (  (x₈ == i₇
                                               ==> 0 <= i₇
                                                && i₇ < i₁₇ + 1)
                                            &&   x₈ == i₇
                                              ||   x₈ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                            && x₈ == i₅₆
                                            && 0 <= i₅₆
                                            && i₅₆ < i₁₇ + 1
                                             ==> (exists i₇: int ::
                                                      b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                      b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                       ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                       ==> false))
                                              || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                      a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                      && __VERIFIER_nondet_int₁₅ == 0
                                                      && i₇ < 100000
                                                      && if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == 0)
                                              || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                      a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                      && (__VERIFIER_nondet_int₁₅ == 0
                                                         ==> false))))
                                    && (forall x₈: int ::
                                            (exists i₇: int, i₅₇: int ::
                                                    if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1
                                                    && x₈ == i₅₇
                                                    && 0 <= i₅₇
                                                    && i₅₇ < i₁₇ + 1)
                                            || a₁₈[i₁₇ := 0][i₁₇ := 1][x₈] == a[x₈])
                                    && (forall x₉: int, i₇: int ::
                                          (  x₉ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₁₇ + 1
                                             ==> (exists i₇: int ::
                                                      b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                       ==> false))
                                              || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                      a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                      && __VERIFIER_nondet_int₁₅ == 0
                                                      && i₇ < 100000
                                                      && x₉ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₇ + 1
                                                      && b₁₉[i₁₇ := i₁₇ % 2][x₉] == i₇ % 2)))
                                    && (forall x₉: int ::
                                            (exists i₇: int ::
                                                    x₉ == i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₇ + 1)
                                            || b₁₉[i₁₇ := i₁₇ % 2][x₉] == b[x₉])
                                    && (forall x₁₀: int, i₇: int ::
                                          (  x₁₀ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₁₇ + 1
                                             ==> (exists i₇: int ::
                                                      b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇ := 1][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                      b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₁₇ := 1][i₇ := 0][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₁₇ := i₁₇ % 2][i₇ := i₇ % 2][i₇] == 0
                                                       ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₁₇ := i₁₇ % 2][i₇] == 0
                                                       ==> false))))
                                    && (forall x₁₀: int ::
                                            (exists i₇: int ::
                                                    x₁₀ == i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₇ + 1)
                                            || c₂₀[x₁₀] == c[x₁₀])
                                    && (forall i₇: int ::
                                          (  0 <= i₇
                                            && i₇ < i₁₇ + 1
                                             ==> i₇ < 100000))))
                            &&   __VERIFIER_nondet_int₁ == 0
                              ||     a₁₈[i₁₇ := 0][i₁₇] == 0
                                  ||   (b₁₉[i₁₇] == 0
                                       ==> 0 <= i₁₇ + 1
                                        && i₁₇ + 1 <= 100000
                                        && (forall x₈: int, i₇: int, i₅₈: int ::
                                              (  (x₈ == i₇
                                                   ==> 0 <= i₇
                                                    && i₇ < i₁₇ + 1)
                                                &&   x₈ == i₇
                                                  ||   x₈ == i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₇ + 1
                                                && x₈ == i₅₈
                                                && 0 <= i₅₈
                                                && i₅₈ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                          b₁₉[i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇] == 0
                                                           ==> false))
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                          && __VERIFIER_nondet_int₁₅ == 0
                                                          && i₇ < 100000
                                                          && if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][x₈] == 0)
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                          && (__VERIFIER_nondet_int₁₅ == 0
                                                             ==> false))))
                                        && (forall x₈: int ::
                                                (exists i₇: int, i₅₉: int ::
                                                        if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1
                                                        && x₈ == i₅₉
                                                        && 0 <= i₅₉
                                                        && i₅₉ < i₁₇ + 1)
                                                || a₁₈[i₁₇ := 0][x₈] == a[x₈])
                                        && (forall x₉: int, i₇: int ::
                                              (  x₉ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                          && __VERIFIER_nondet_int₁₅ == 0
                                                          && i₇ < 100000
                                                          && x₉ == i₇
                                                          && 0 <= i₇
                                                          && i₇ < i₁₇ + 1
                                                          && b₁₉[x₉] == i₇ % 2)))
                                        && (forall x₉: int ::
                                                (exists i₇: int ::
                                                        x₉ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇ + 1)
                                                || b₁₉[x₉] == b[x₉])
                                        && (forall x₁₀: int, i₇: int ::
                                              (  x₁₀ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                          b₁₉[i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇] == 0
                                                           ==> false))))
                                        && (forall x₁₀: int ::
                                                (exists i₇: int ::
                                                        x₁₀ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇ + 1)
                                                || c₂₀[i₁₇ := 0][x₁₀] == c[x₁₀])
                                        && (forall i₇: int ::
                                              (  0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> i₇ < 100000)))
                                    &&   b₁₉[i₁₇] == 0
                                      ||   0 <= i₁₇ + 1
                                        && i₁₇ + 1 <= 100000
                                        && (forall x₈: int, i₇: int, i₆₀: int ::
                                              (  (x₈ == i₇
                                                   ==> 0 <= i₇
                                                    && i₇ < i₁₇ + 1)
                                                &&   x₈ == i₇
                                                  ||   x₈ == i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₇ + 1
                                                && x₈ == i₆₀
                                                && 0 <= i₆₀
                                                && i₆₀ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                          b₁₉[i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇] == 0
                                                           ==> false))
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                          && __VERIFIER_nondet_int₁₅ == 0
                                                          && i₇ < 100000
                                                          && if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][x₈] == 0)
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                          && (__VERIFIER_nondet_int₁₅ == 0
                                                             ==> false))))
                                        && (forall x₈: int ::
                                                (exists i₇: int, i₆₁: int ::
                                                        if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1
                                                        && x₈ == i₆₁
                                                        && 0 <= i₆₁
                                                        && i₆₁ < i₁₇ + 1)
                                                || a₁₈[i₁₇ := 0][x₈] == a[x₈])
                                        && (forall x₉: int, i₇: int ::
                                              (  x₉ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                          a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                          && __VERIFIER_nondet_int₁₅ == 0
                                                          && i₇ < 100000
                                                          && x₉ == i₇
                                                          && 0 <= i₇
                                                          && i₇ < i₁₇ + 1
                                                          && b₁₉[x₉] == i₇ % 2)))
                                        && (forall x₉: int ::
                                                (exists i₇: int ::
                                                        x₉ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇ + 1)
                                                || b₁₉[x₉] == b[x₉])
                                        && (forall x₁₀: int, i₇: int ::
                                              (  x₁₀ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> (exists i₇: int ::
                                                          b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                          b₁₉[i₇] == 0
                                                          && (a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                             ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                           ==> false))
                                                  || (exists i₇: int ::
                                                        (b₁₉[i₇] == 0
                                                           ==> false))))
                                        && (forall x₁₀: int ::
                                                (exists i₇: int ::
                                                        x₁₀ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₇ + 1)
                                                || c₂₀[i₁₇ := 1][x₁₀] == c[x₁₀])
                                        && (forall i₇: int ::
                                              (  0 <= i₇
                                                && i₇ < i₁₇ + 1
                                                 ==> i₇ < 100000))
                                && (a₁₈[i₁₇ := 0][i₁₇] == 0
                                   ==> 0 <= i₁₇ + 1
                                    && i₁₇ + 1 <= 100000
                                    && (forall x₈: int, i₇: int, i₆₂: int ::
                                          (  (x₈ == i₇
                                               ==> 0 <= i₇
                                                && i₇ < i₁₇ + 1)
                                            &&   x₈ == i₇
                                              ||   x₈ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₇ + 1
                                            && x₈ == i₆₂
                                            && 0 <= i₆₂
                                            && i₆₂ < i₁₇ + 1
                                             ==> (exists i₇: int ::
                                                      b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                      b₁₉[i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                       ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₇] == 0
                                                       ==> false))
                                              || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                      a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                      && __VERIFIER_nondet_int₁₅ == 0
                                                      && i₇ < 100000
                                                      && if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1 && a₁₈[i₁₇ := 0][x₈] == 0)
                                              || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                      a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                      && (__VERIFIER_nondet_int₁₅ == 0
                                                         ==> false))))
                                    && (forall x₈: int ::
                                            (exists i₇: int, i₆₃: int ::
                                                    if(x₈ == i₇) then 0 <= i₇ && i₇ < i₁₇ + 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i₁₇ + 1
                                                    && x₈ == i₆₃
                                                    && 0 <= i₆₃
                                                    && i₆₃ < i₁₇ + 1)
                                            || a₁₈[i₁₇ := 0][x₈] == a[x₈])
                                    && (forall x₉: int, i₇: int ::
                                          (  x₉ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₁₇ + 1
                                             ==> (exists i₇: int ::
                                                      b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                       ==> false))
                                              || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                      a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                      && __VERIFIER_nondet_int₁₅ == 0
                                                      && i₇ < 100000
                                                      && x₉ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₇ + 1
                                                      && b₁₉[x₉] == i₇ % 2)))
                                    && (forall x₉: int ::
                                            (exists i₇: int ::
                                                    x₉ == i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₇ + 1)
                                            || b₁₉[x₉] == b[x₉])
                                    && (forall x₁₀: int, i₇: int ::
                                          (  x₁₀ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₁₇ + 1
                                             ==> (exists i₇: int ::
                                                      b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₇ := 0][i₇ := 1][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                      b₁₉[i₇] == 0
                                                      && (a₁₈[i₁₇ := 0][i₇ := 0][i₇] == 0
                                                         ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₇ := i₇ % 2][i₇] == 0
                                                       ==> false))
                                              || (exists i₇: int ::
                                                    (b₁₉[i₇] == 0
                                                       ==> false))))
                                    && (forall x₁₀: int ::
                                            (exists i₇: int ::
                                                    x₁₀ == i₇
                                                    && 0 <= i₇
                                                    && i₇ < i₁₇ + 1)
                                            || c₂₀[x₁₀] == c[x₁₀])
                                    && (forall i₇: int ::
                                          (  0 <= i₇
                                            && i₇ < i₁₇ + 1
                                             ==> i₇ < 100000)))))
                  &&   i₁₇ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall i₁₅: int ::
                            (  0 <= i₁₅
                              && i₁₅ < 0
                               ==> i₁₅ < 100000))
                      && (forall i₂₁: int ::
                            (  0 <= i₂₁
                              && i₂₁ <= 100000
                              && (forall i₁₅: int ::
                                    (  0 <= i₁₅
                                      && i₁₅ < i₂₁
                                       ==> i₁₅ < 100000))
                               ==> (i₂₁ < 100000
                                 ==> (i₂₁ == 15000
                                     ==> (a₁₈[15000 := 1][i₂₁] == 1
                                       ==> false))
                                  &&   i₂₁ == 15000
                                    ||   0 <= i₂₁ + 1
                                      && i₂₁ + 1 <= 100000
                                      && (forall i₁₅: int ::
                                            (  0 <= i₁₅
                                              && i₁₅ < i₂₁ + 1
                                               ==> i₁₅ < 100000))))))));

