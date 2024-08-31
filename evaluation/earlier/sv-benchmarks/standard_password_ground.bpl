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
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₇: int ::
            ((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
               ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                      i₆ < 100000
                      && x₇ == i₆
                      && old(i) <= i₆
                      && i₆ < i
                      && password[x₇] == __VERIFIER_nondet_int₁₄)))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
            )
               ==> password[x₇] == old(password[x₇])))
      && (forall x₈: int ::
            ((exists i₆: int ::
                    x₈ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
               ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                      i₆ < 100000
                      && x₈ == i₆
                      && old(i) <= i₆
                      && i₆ < i
                      && guess[x₈] == __VERIFIER_nondet_int₂₅)))
      && (forall x₈: int ::
            (!((exists i₆: int ::
                    x₈ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
            )
               ==> guess[x₈] == old(guess[x₈])))
      && (forall i₆: int ::
            (  old(i₆) <= i₆
              && old(i) <= i₆
              && i₆ < i
               ==> i₆ < 100000));
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
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall i₁₃: int ::
            (  old(i₁₃) <= i₁₃
              && old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000));
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
      invariant true
        && old(x) <= x
        && x <= 100000
        && (forall x₁₇: int ::
              (  old(x₁₇) <= x₁₇
                && old(x) <= x₁₇
                && x₁₇ < x
                 ==> x₁₇ < 100000));
    {
      assert password[x] == guess[x];
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

