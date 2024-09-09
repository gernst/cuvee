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
  var max: int := 0;
  var j: int := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant old(j) <= j
      && (forall j₃: int ::
            (  old(j) <= j₃
              && j₃ < j
               ==> (exists __VERIFIER_nondet_int₁₂: int ::
                      j₃ < 100000
                      && a[j₃] == __VERIFIER_nondet_int₁₂)))
      && (forall j₃: int ::
            (!(  old(j) <= j₃
              && j₃ < j
            )
               ==> a[j₃] == old(a)[j₃]));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[j := __VERIFIER_nondet_int₁];
    j := j + 1;
  }
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall max₆: int, i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> max₆ < a[i₇]
                  && i₇ < 100000
                ||   !(max₆ < a[i₇]
                  )
                  && i₇ < 100000));
  {
    if(max < a[i]) {
      max := a[i];
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
    assert a[x] <= max;
    x := x + 1;
  }
  c#result := 0;
  return;
}

