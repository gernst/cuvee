data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, N: int ::
        0 <= 0
        && 0 <= N
        && (forall i₂: int ::
              (  0 <= i₂
                && i₂ < 0
                 ==> i₂ < N))
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ <= N
                && (forall i₂: int ::
                      (  0 <= i₂
                        && i₂ < i₂₄
                         ==> i₂ < N))
                 ==> (i₂₄ < N
                   ==> (x[i₂₄] % 2 == 0
                       ==> 0 <= i₂₄ + 1
                        && i₂₄ + 1 <= N
                        && (forall i₂: int ::
                              (  0 <= i₂
                                && i₂ < i₂₄ + 1
                                 ==> i₂ < N)))
                    &&   x[i₂₄] % 2 == 0
                      ||   0 <= i₂₄ + 1
                        && i₂₄ + 1 <= N
                        && (forall i₂: int ::
                              (  0 <= i₂
                                && i₂ < i₂₄ + 1
                                 ==> i₂ < N))))));

