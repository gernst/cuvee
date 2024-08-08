data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall x: [int]int, N: int ::
        0 <= 0
        && 0 <= N
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 0 <= i₃
                && i₃ < 0
                 ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                        i₃ < N
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < 0
                        && x[x₄] == __VERIFIER_nondet_int₁₂)))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 0 <= i₃
                        && i₃ < 0)
                || x[x₄] == x[x₄])
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < 0
                 ==> i₃ < N))
        && (forall x₄₇: [int]int, i₄₈: int ::
              (  0 <= i₄₈
                && i₄₈ <= N
                && (forall x₄: int, i₃: int ::
                      (  x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₄₈
                         ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                                i₃ < N
                                && x₄ == i₃
                                && 0 <= i₃
                                && i₃ < i₄₈
                                && x₄₇[x₄] == __VERIFIER_nondet_int₁₂)))
                && (forall x₄: int ::
                        (exists i₃: int ::
                                x₄ == i₃
                                && 0 <= i₃
                                && i₃ < i₄₈)
                        || x₄₇[x₄] == x[x₄])
                && (forall i₃: int ::
                      (  0 <= i₃
                        && i₃ < i₄₈
                         ==> i₃ < N))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                      (i₄₈ < N
                         ==> 0 <= i₄₈ + 1
                          && i₄₈ + 1 <= N
                          && (forall x₄: int, i₃: int ::
                                (  x₄ == i₃
                                  && 0 <= i₃
                                  && i₃ < i₄₈ + 1
                                   ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                                          i₃ < N
                                          && x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₄₈ + 1
                                          && x₄₇[i₄₈ := __VERIFIER_nondet_int₁][x₄] == __VERIFIER_nondet_int₁₂)))
                          && (forall x₄: int ::
                                  (exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₄₈ + 1)
                                  || x₄₇[i₄₈ := __VERIFIER_nondet_int₁][x₄] == x[x₄])
                          && (forall i₃: int ::
                                (  0 <= i₃
                                  && i₃ < i₄₈ + 1
                                   ==> i₃ < N)))))));

goal (forall N: int ::
        0 <= 0
        && 0 <= 0
        && 0 <= N
        && (forall cnt₁₀: int, i₁₁: int ::
              (  0 <= cnt₁₀
                && 0 <= i₁₁
                && cnt₁₀ < 0
                && i₁₁ < 0
                 ==> i₁₁ < N))
        && (forall cnt₅₂: int, i₅₃: int ::
              (  0 <= cnt₅₂
                && 0 <= i₅₃
                && i₅₃ <= N
                && (forall cnt₁₀: int, i₁₁: int ::
                      (  0 <= cnt₁₀
                        && 0 <= i₁₁
                        && cnt₁₀ < cnt₅₂
                        && i₁₁ < i₅₃
                         ==> i₁₁ < N))
                 ==> (i₅₃ < N
                   ==> (N / 2 < i₅₃
                       ==> 0 <= cnt₅₂ + 1
                        && 0 <= i₅₃ + 1
                        && i₅₃ + 1 <= N
                        && (forall cnt₁₀: int, i₁₁: int ::
                              (  0 <= cnt₁₀
                                && 0 <= i₁₁
                                && cnt₁₀ < cnt₅₂ + 1
                                && i₁₁ < i₅₃ + 1
                                 ==> i₁₁ < N)))
                    &&   N / 2 < i₅₃
                      ||   0 <= cnt₅₂
                        && 0 <= i₅₃ + 1
                        && i₅₃ + 1 <= N
                        && (forall cnt₁₀: int, i₁₁: int ::
                              (  0 <= cnt₁₀
                                && 0 <= i₁₁
                                && cnt₁₀ < cnt₅₂
                                && i₁₁ < i₅₃ + 1
                                 ==> i₁₁ < N))))));

