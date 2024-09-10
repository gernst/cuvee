data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure mapavg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 10000)
    decreases 10000 - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < 10000));
  {
    ret := ret + i + x[i];
    i := i + 1;
  }
  c#result := ret / 10000;
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
  while(i < 10000)
    decreases 10000 - i;
    invariant old(i) <= i
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> (exists nondet_int₂₁₂: int ::
                      -2147483648 <= nondet_int₂₁₂
                      && nondet_int₂₁₂ < 2147483648
                      && i₁₃ < 10000
                      && x[i₁₃] == nondet_int₂₁₂)))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> x[i₁₃] == old(x)[i₁₃]));
  {
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    x[i] := nondet_int₂;
    i := i + 1;
  }
  var mapavg₄: int;
  mapavg₄ := call mapavg(x);
  ret := mapavg₄;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var mapavg₅: int;
  mapavg₅ := call mapavg(x);
  ret2 := mapavg₅;
  temp := x[0];
  var i: int := 0;
  while(i < 10000 - 1)
    decreases 10000 - 1 - i;
    invariant old(i) <= i
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 9999
                && x[i₁₈] == old(x)[1 + i₁₈]))
      && (forall i₁₈: int ::
            (!(  old(i) <= i₁₈
              && i₁₈ < i
            )
               ==> x[i₁₈] == old(x)[i₁₈]));
  {
    x[i] := x[i + 1];
    i := i + 1;
  }
  x[(10000 - 1)] := temp;
  var mapavg₇: int;
  mapavg₇ := call mapavg(x);
  ret5 := mapavg₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

