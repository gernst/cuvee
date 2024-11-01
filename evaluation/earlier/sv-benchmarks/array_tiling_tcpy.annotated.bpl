data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var S: int;
  assume -2147483648 <= S && S < 2147483648;
  assume 1 < S;
  assume S < 1073741823;
  var i: int;
  var a: [int]int;
  var acopy: [int]int;
  i := 0;
  while(i < S)
    decreases S - i;
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < S
                && acopy[i₅] == a[i₅]
                && (-1 + -i₅ + 2 * S != i₅
                   ==> acopy[-1 + -i₅ + 2 * S] == a[1 + -i₅ + 2 * S])))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> acopy[i₅] == old(acopy)[i₅]
                && acopy[-1 + -i₅ + 2 * S] == old(acopy)[-1 + -i₅ + 2 * S]));
  {
    acopy[((2 * S) - (i + 1))] := a[2 * S - i + 1];
    acopy[i] := a[i];
    i := i + 1;
  }
  i := 0;
  while(i < 2 * S)
    decreases 2 * S - i;
    invariant old(i) <= i
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ < 2 * S));
  {
    assert acopy[i] == a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

