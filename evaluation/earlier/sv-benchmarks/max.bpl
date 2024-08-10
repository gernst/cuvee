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
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < 0
                 ==> i₅ < N))
        && (forall ret₃₁: int, i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ <= N
                && (forall i₅: int ::
                      (  0 <= i₅
                        && i₅ < i₃₂
                         ==> i₅ < N))
                 ==> (i₃₂ < N
                   ==> (ret₃₁ < x[i₃₂]
                       ==> 0 <= i₃₂ + 1
                        && i₃₂ + 1 <= N
                        && (forall i₅: int ::
                              (  0 <= i₅
                                && i₅ < i₃₂ + 1
                                 ==> i₅ < N)))
                    &&   ret₃₁ < x[i₃₂]
                      ||   0 <= i₃₂ + 1
                        && i₃₂ + 1 <= N
                        && (forall i₅: int ::
                              (  0 <= i₅
                                && i₅ < i₃₂ + 1
                                 ==> i₅ < N))))));

