data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N: int ::
        0 <= 0
        && 0 <= N
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < 0
                 ==> i₄ < N))
        && (forall i₃₃: int ::
              (  0 <= i₃₃
                && i₃₃ <= N
                && (forall i₄: int ::
                      (  0 <= i₄
                        && i₄ < i₃₃
                         ==> i₄ < N))
                 ==> (i₃₃ < N
                   ==> 0 <= i₃₃ + 1
                    && i₃₃ + 1 <= N
                    && (forall i₄: int ::
                          (  0 <= i₄
                            && i₄ < i₃₃ + 1
                             ==> i₄ < N))))));

