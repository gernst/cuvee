data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure avg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 20)
    decreases 20 - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < 20));
  {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret / 20;
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
  while(i < 20)
    decreases 20 - i;
    invariant old(i) <= i
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> (exists nondet_int₂₁₂: int ::
                      -2147483648 <= nondet_int₂₁₂
                      && nondet_int₂₁₂ < 2147483648
                      && i₁₃ < 20
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
  var avg₄: int;
  avg₄ := call avg(x);
  ret := avg₄;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var avg₅: int;
  avg₅ := call avg(x);
  ret2 := avg₅;
  temp := x[0];
  var i: int := 0;
  while(i < 20 - 1)
    decreases 20 - 1 - i;
    invariant old(i) <= i
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 19
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
  x[(20 - 1)] := temp;
  var avg₇: int;
  avg₇ := call avg(x);
  ret5 := avg₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

