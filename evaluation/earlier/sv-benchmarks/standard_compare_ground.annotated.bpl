data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var j: int := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant true
      && old(j) <= j
      && j <= 100000
      && (forall x₆: int ::
            ((exists j₅: int ::
                    x₆ == j₅
                    && old(j) <= j₅
                    && j₅ < j)
               ==> (exists __VERIFIER_nondet_int₁₃: int, j₅: int ::
                      j₅ < 100000
                      && x₆ == j₅
                      && old(j) <= j₅
                      && j₅ < j
                      && a[x₆] == __VERIFIER_nondet_int₁₃)))
      && (forall x₆: int ::
            (!((exists j₅: int ::
                    x₆ == j₅
                    && old(j) <= j₅
                    && j₅ < j)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall x₇: int ::
            ((exists j₅: int ::
                    x₇ == j₅
                    && old(j) <= j₅
                    && j₅ < j)
               ==> (exists __VERIFIER_nondet_int₂₄: int, j₅: int ::
                      j₅ < 100000
                      && x₇ == j₅
                      && old(j) <= j₅
                      && j₅ < j
                      && b[x₇] == __VERIFIER_nondet_int₂₄)))
      && (forall x₇: int ::
            (!((exists j₅: int ::
                    x₇ == j₅
                    && old(j) <= j₅
                    && j₅ < j)
            )
               ==> b[x₇] == old(b[x₇])))
      && (forall j₅: int ::
            (  old(j) <= j₅
              && j₅ < j
               ==> j₅ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[j := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    b := b[j := __VERIFIER_nondet_int₂];
    j := j + 1;
  }
  var i: int := 0;
  var rv: int := 1;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < 100000));
  {
    if(a[i] != b[i]) {
      rv := 0;
    }
    i := i + 1;
  }
  if(rv != 0) {
    var x: int;
    x := 0;
    while(x < 100000)
      decreases 100000 - x;
      invariant true
        && old(x) <= x
        && x <= 100000
        && (forall x₁₆: int ::
              (  old(x) <= x₁₆
                && x₁₆ < x
                 ==> x₁₆ < 100000));
    {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

