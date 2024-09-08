data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure mapsum(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < N));
  {
    ret := ret + i + x[i];
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
  modifies N;
{
  havoc N;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var i: int := 0;
    while(i < N)
      decreases N - i;
      invariant old(i) <= i
        && i <= N
        && (forall i₁₄: int ::
              (  old(i) <= i₁₄
                && i₁₄ < i
                 ==> (exists __VERIFIER_nondet_int₂₁₃: int ::
                        i₁₄ < N
                        && x[i₁₄] == __VERIFIER_nondet_int₂₁₃)))
        && (forall i₁₄: int ::
              (!(  old(i) <= i₁₄
                && i₁₄ < i
              )
                 ==> x[i₁₄] == old(x)[i₁₄]));
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
    while(i < N - 1)
      decreases N - 1 - i;
      invariant old(i) <= i
        && i <= -1 + N
        && (forall i₂₃: int ::
              (  old(i) <= i₂₃
                && i₂₃ < i
                 ==> i₂₃ < -1 + N
                  && x[i₂₃] == old(x)[1 + i₂₃]))
        && (forall i₂₃: int ::
              (!(  old(i) <= i₂₃
                && i₂₃ < i
              )
                 ==> x[i₂₃] == old(x)[i₂₃]));
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var mapsum₇: int;
    mapsum₇ := call mapsum(x);
    ret5 := mapsum₇;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

