data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var a: [int]int;
  var b: [int]int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && i <= 100000
      && (forall x₆: int ::
            ((exists i₅: int ::
                  x₆ == i₅)
               ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                        __VERIFIER_nondet_int₁₄ == 10
                        && i₅ < 100000
                        && x₆ == i₅
                        && a[x₆] == __VERIFIER_nondet_int₁₄)
                || (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                        __VERIFIER_nondet_int₁₄ != 10
                        && i₅ < 100000
                        && x₆ == i₅
                        && a[x₆] == __VERIFIER_nondet_int₁₄)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                  x₆ == i₅)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall x₇: int ::
            ((exists i₅: int ::
                  x₇ == i₅)
               ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                      __VERIFIER_nondet_int₁₄ == 10
                      && i₅ < 100000
                      && x₇ == i₅
                      && b[x₇] == 20)))
      && (forall x₇: int ::
            (!((exists i₅: int ::
                  x₇ == i₅)
            )
               ==> b[x₇] == old(b[x₇])))
      && (forall i₅: int ::
            i₅ < 100000);
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    if(a[i] == 10) {
      b := b[i := 20];
    }
    i := i + 2;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && i <= 100000
      && (forall i₁₁: int ::
            i₁₁ < 100000);
  {
    if(a[i] == 10) {
      assert b[i] == 20;
    }
    i := i + 2;
  }
}

