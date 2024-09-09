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
  var min: int := 0;
  var i: int := 0;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₃: int ::
            (  old(i) <= i₃
              && i₃ < i
               ==> (exists __VERIFIER_nondet_int₁₂: int ::
                      i₃ < 100000
                      && a[i₃] == __VERIFIER_nondet_int₁₂)))
      && (forall i₃: int ::
            (!(  old(i) <= i₃
              && i₃ < i
            )
               ==> a[i₃] == old(a)[i₃]));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall min₆: int, i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> a[i₇] < min₆
                  && i₇ < 100000
                ||   !(a[i₇] < min₆
                  )
                  && i₇ < 100000));
  {
    if(a[i] < min) {
      min := a[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₁₁: int ::
            (  old(x) <= x₁₁
              && x₁₁ < x
               ==> x₁₁ < 100000));
  {
    assert min <= a[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

