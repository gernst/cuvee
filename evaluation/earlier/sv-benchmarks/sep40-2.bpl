data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sep(x: [int]int)
  returns (c#result: int)
{
  var ret: int := 0;
  var i: int := 0;
  while(i < 40)
    decreases 40 - i;
    invariant true
      && old(i) <= i
      && i <= 40
      && (forall i₂: int ::
            (  old(i₂) <= i₂
              && old(i) <= i₂
              && i₂ < i
               ==> i₂ < 40));
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
  var sep₄: int;
  sep₄ := call sep(x);
  ret := sep₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₅: int;
  sep₅ := call sep(x);
  ret2 := sep₅;
  temp := x[0];
  var i: int := 0;
  while(i < 40 - 1)
    decreases 40 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 39
      && (forall x₁₃: int ::
            ((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && old(i) <= i₁₂
                    && i₁₂ < i)
               ==> (exists i₁₂: int ::
                      i₁₂ < 39
                      && x₁₃ == i₁₂
                      && old(i) <= i₁₂
                      && i₁₂ < i
                      && x[x₁₃] == old(x)[1 + i₁₂])))
      && (forall x₁₃: int ::
            (!((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && old(i) <= i₁₂
                    && i₁₂ < i)
            )
               ==> x[x₁₃] == old(x[x₁₃])))
      && (forall i₁₂: int ::
            (  old(i₁₂) <= i₁₂
              && old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < 39));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var sep₇: int;
  sep₇ := call sep(x);
  ret5 := sep₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

