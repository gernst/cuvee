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

goal (forall __VERIFIER_nondet_int₁: int ::
      0 <= __VERIFIER_nondet_int₁);

