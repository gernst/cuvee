data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int ::
        1 <= 1
        && 1 <= N
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < 1
                 ==> i₄ < N))
        && (forall i₃₃: int ::
              (  1 <= i₃₃
                && i₃₃ <= N
                && (forall i₄: int ::
                      (  1 <= i₄
                        && i₄ < i₃₃
                         ==> i₄ < N))
                 ==> (i₃₃ < N
                   ==> 1 <= i₃₃ + 1
                    && i₃₃ + 1 <= N
                    && (forall i₄: int ::
                          (  1 <= i₄
                            && i₄ < i₃₃ + 1
                             ==> i₄ < N))))));

