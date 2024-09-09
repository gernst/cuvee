data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var password: [int]int;
  var guess: [int]int;
  var i: int;
  var result: int := 1;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> (exists __VERIFIER_nondet_int₁₄: int, __VERIFIER_nondet_int₂₅: int ::
                      i₆ < 100000
                      && password[i₆] == __VERIFIER_nondet_int₁₄
                      && guess[i₆] == __VERIFIER_nondet_int₂₅)))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> password[i₆] == old(password)[i₆]
                && guess[i₆] == old(guess)[i₆]));
  {
    var __VERIFIER_nondet_int₁: int;
    password := password[i := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    guess := guess[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> password[i₁₁] != guess[i₁₁]
                  && i₁₁ < 100000
                ||   password[i₁₁] == guess[i₁₁]
                  && i₁₁ < 100000));
  {
    if(password[i] != guess[i]) {
      result := 0;
    }
    i := i + 1;
  }
  if(result != 0) {
    var x: int;
    x := 0;
    while(x < 100000)
      decreases 100000 - x;
      invariant old(x) <= x
        && (forall x₁₅: int ::
              (  old(x) <= x₁₅
                && x₁₅ < x
                 ==> x₁₅ < 100000));
    {
      assert password[x] == guess[x];
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

