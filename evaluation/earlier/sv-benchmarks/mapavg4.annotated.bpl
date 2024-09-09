data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure mapavg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < 100000));
  {
    ret := ret + i + x[i];
    i := i + 1;
  }
  c#result := ret / 100000;
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
  var mapavg₄: int;
  mapavg₄ := call mapavg(x);
  ret := mapavg₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapavg₅: int;
  mapavg₅ := call mapavg(x);
  ret2 := mapavg₅;
  temp := x[0];
  var i: int := 0;
  while(i < 100000 - 1)
    decreases 100000 - 1 - i;
    invariant old(i) <= i
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
  var mapavg₇: int;
  mapavg₇ := call mapavg(x);
  ret5 := mapavg₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

