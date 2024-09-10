data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure max(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 20)
    decreases 20 - i;
    invariant old(i) <= i
      && (forall ret₄: int, i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> ret₄ < x[i₅]
                  && i₅ < 20
                ||   !(ret₄ < x[i₅]
                  )
                  && i₅ < 20));
  {
    var x₁: int;
    if(ret < x[i]) {
      x₁ := x[i];
    } else {
      x₁ := ret;
    }
    ret := x₁;
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
  while(i < 20)
    decreases 20 - i;
    invariant old(i) <= i
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> (exists nondet_int₃₁₃: int ::
                      -2147483648 <= nondet_int₃₁₃
                      && nondet_int₃₁₃ < 2147483648
                      && i₁₄ < 20
                      && x[i₁₄] == nondet_int₃₁₃)))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> x[i₁₄] == old(x)[i₁₄]));
  {
    var nondet_int₃: int;
    assume -2147483648 <= nondet_int₃ && nondet_int₃ < 2147483648;
    x[i] := nondet_int₃;
    i := i + 1;
  }
  var max₅: int;
  max₅ := call max(x);
  ret := max₅;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var max₆: int;
  max₆ := call max(x);
  ret2 := max₆;
  temp := x[0];
  var i: int := 0;
  while(i < 20 - 1)
    decreases 20 - 1 - i;
    invariant old(i) <= i
      && (forall i₁₉: int ::
            (  old(i) <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < 19
                && x[i₁₉] == old(x)[1 + i₁₉]))
      && (forall i₁₉: int ::
            (!(  old(i) <= i₁₉
              && i₁₉ < i
            )
               ==> x[i₁₉] == old(x)[i₁₉]));
  {
    x[i] := x[i + 1];
    i := i + 1;
  }
  x[(20 - 1)] := temp;
  var max₈: int;
  max₈ := call max(x);
  ret5 := max₈;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

