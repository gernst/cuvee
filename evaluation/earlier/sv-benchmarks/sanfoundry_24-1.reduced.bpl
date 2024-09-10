data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall i: int ::
      i % 2 == 0);

goal {:named "assert"} (forall i: int ::
      (i % 2 == 0
         ==> false));

