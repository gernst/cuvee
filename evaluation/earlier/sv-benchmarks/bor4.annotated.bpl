data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure bor(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < 100000));
  {
    res := c#bitor(res, x[i]);
    i := i + 1;
  }
  c#result := res;
  return;
}

procedure main()
  returns (c#result: int)
{
  var x: [int]int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> (exists __VERIFIER_nondet_int₂₁₂: int ::
                      i₁₃ < 100000
                      && x[i₁₃] == __VERIFIER_nondet_int₂₁₂)))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> x[i₁₃] == old(x)[i₁₃]));
  {
    var __VERIFIER_nondet_int₂: int;
    x := x[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var bor₄: int;
  bor₄ := call bor(x);
  ret := bor₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bor₅: int;
  bor₅ := call bor(x);
  ret2 := bor₅;
  temp := x[0];
  var i: int := 0;
  while(i < 100000 - 1)
    decreases 100000 - 1 - i;
    invariant old(i) <= i
      && i <= 99999
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 99999
                && x[i₁₈] == old(x)[1 + i₁₈]))
      && (forall i₁₈: int ::
            (!(  old(i) <= i₁₈
              && i₁₈ < i
            )
               ==> x[i₁₈] == old(x)[i₁₈]));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[100000 - 1 := temp];
  var bor₇: int;
  bor₇ := call bor(x);
  ret5 := bor₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

