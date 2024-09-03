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
    invariant true
      && 0 <= i
      && i <= S
      && (forall x₇: int ::
            ((exists i₆: int ::
                  if(x₇ == i₆) then 0 <= i₆ && i₆ < i else x₇ == 1 + 2 * S + -i₆)
               ==> (exists i₆: int ::
                      i₆ < S
                      && if(x₇ == i₆) then 0 <= i₆ && i₆ < i && acopy[x₇] == a[i₆] else x₇ == 1 + 2 * S + -i₆ && acopy[x₇] == a[1 + 2 * S + -i₆])))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                  if(x₇ == i₆) then 0 <= i₆ && i₆ < i else x₇ == 1 + 2 * S + -i₆)
            )
               ==> acopy[x₇] == old(acopy[x₇])))
      && (forall i₆: int ::
            (  0 <= i₆
              && i₆ < i
               ==> i₆ < S));
  {
    acopy := acopy[2 * S - i + 1 := a[2 * S - i + 1]];
    acopy := acopy[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 2 * S)
    decreases 2 * S - i;
    invariant true
      && 0 <= i
      && i <= 2 * S
      && (forall i₁₀: int ::
            (  0 <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < 2 * S));
  {
    assert acopy[i] == a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

