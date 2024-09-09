data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var __VERIFIER_nondet_int₁: int;
  var S: int;
  S := __VERIFIER_nondet_int₁;
  assume 1 < S;
  assume S < 1073741823;
  var i: int;
  var a: [int]int;
  var acopy: [int]int;
  i := 0;
  while(i < S)
    decreases S - i;
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> i₆ < S
                && acopy[i₆] == a[i₆]
                && (1 + 2 * S + -i₆ != i₆
                   ==> acopy[1 + 2 * S + -i₆] == a[1 + 2 * S + -i₆])));
  {
    acopy := acopy[2 * S - i + 1 := a[2 * S - i + 1]];
    acopy := acopy[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 2 * S)
    decreases 2 * S - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < 2 * S));
  {
    assert acopy[i] == a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

