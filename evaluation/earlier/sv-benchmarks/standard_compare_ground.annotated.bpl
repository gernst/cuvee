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
    invariant old(j) <= j
      && (forall j₅: int ::
            (  old(j) <= j₅
              && j₅ < j
               ==> (exists __VERIFIER_nondet_int₁₃: int, __VERIFIER_nondet_int₂₄: int ::
                      j₅ < 100000
                      && a[j₅] == __VERIFIER_nondet_int₁₃
                      && b[j₅] == __VERIFIER_nondet_int₂₄)))
      && (forall j₅: int ::
            (!(  old(j) <= j₅
              && j₅ < j
            )
               ==> a[j₅] == old(a)[j₅]
                && b[j₅] == old(b)[j₅]));
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
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> a[i₁₀] != b[i₁₀]
                  && i₁₀ < 100000
                ||   a[i₁₀] == b[i₁₀]
                  && i₁₀ < 100000));
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
      invariant old(x) <= x
        && (forall x₁₄: int ::
              (  old(x) <= x₁₄
                && x₁₄ < x
                 ==> x₁₄ < 100000));
    {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

