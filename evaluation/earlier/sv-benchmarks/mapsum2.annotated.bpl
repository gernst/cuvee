data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure mapsum(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 1000)
    decreases 1000 - i;
    invariant old(i) <= i
      && i <= 1000
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < 1000));
  {
    ret := ret + i + x[i];
    i := i + 1;
  }
  c#result := ret;
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
  while(i < 1000)
    decreases 1000 - i;
    invariant old(i) <= i
      && i <= 1000
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> (exists __VERIFIER_nondet_int₂₁₂: int ::
                      i₁₃ < 1000
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
  var mapsum₄: int;
  mapsum₄ := call mapsum(x);
  ret := mapsum₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapsum₅: int;
  mapsum₅ := call mapsum(x);
  ret2 := mapsum₅;
  temp := x[0];
  var i: int := 0;
  while(i < 1000 - 1)
    decreases 1000 - 1 - i;
    invariant old(i) <= i
      && i <= 999
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 999
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
  x := x[1000 - 1 := temp];
  var mapsum₇: int;
  mapsum₇ := call mapsum(x);
  ret5 := mapsum₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

