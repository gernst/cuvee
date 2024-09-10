data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sep(x: [int]int)
  returns (c#result: int)
{
  var ret: int := 0;
  var i: int := 0;
  while(i < 40)
    decreases 40 - i;
    invariant old(i) <= i
      && (forall i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> x[i₂] % 2 == 0
                  && i₂ < 40
                ||   x[i₂] % 2 != 0
                  && i₂ < 40));
  {
    if(x[i] % 2 == 0) {
      ret := ret + 1;
    } else {
      ret := ret - 1;
    }
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
  while(i < 40)
    decreases 40 - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> (exists nondet_int₄₁₀: int ::
                      -2147483648 <= nondet_int₄₁₀
                      && nondet_int₄₁₀ < 2147483648
                      && i₁₁ < 40
                      && x[i₁₁] == nondet_int₄₁₀)))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> x[i₁₁] == old(x)[i₁₁]));
  {
    var nondet_int₄: int;
    assume -2147483648 <= nondet_int₄ && nondet_int₄ < 2147483648;
    x[i] := nondet_int₄;
    i := i + 1;
  }
  var sep₆: int;
  sep₆ := call sep(x);
  ret := sep₆;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var sep₇: int;
  sep₇ := call sep(x);
  ret2 := sep₇;
  temp := x[0];
  var i: int := 0;
  while(i < 40 - 1)
    decreases 40 - 1 - i;
    invariant old(i) <= i
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < 39
                && x[i₁₆] == old(x)[1 + i₁₆]))
      && (forall i₁₆: int ::
            (!(  old(i) <= i₁₆
              && i₁₆ < i
            )
               ==> x[i₁₆] == old(x)[i₁₆]));
  {
    x[i] := x[i + 1];
    i := i + 1;
  }
  x[(40 - 1)] := temp;
  var sep₉: int;
  sep₉ := call sep(x);
  ret5 := sep₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

