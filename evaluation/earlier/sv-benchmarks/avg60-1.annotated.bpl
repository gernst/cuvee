data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure avg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 60)
    decreases 60 - i;
    invariant true
      && old(i) <= i
      && i <= 60
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < 60));
  {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret / 60;
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
  while(i < 60)
    decreases 60 - i;
    invariant true
      && old(i) <= i
      && i <= 60
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
               ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                      i₁₃ < 60
                      && x₁₄ == i₁₃
                      && old(i) <= i₁₃
                      && i₁₃ < i
                      && x[x₁₄] == __VERIFIER_nondet_int₂₁₂)))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
            )
               ==> x[x₁₄] == old(x[x₁₄])))
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 60));
  {
    var __VERIFIER_nondet_int₂: int;
    x := x[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var avg₄: int;
  avg₄ := call avg(x);
  ret := avg₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₅: int;
  avg₅ := call avg(x);
  ret2 := avg₅;
  temp := x[0];
  var i: int := 0;
  while(i < 60 - 1)
    decreases 60 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 59
      && (forall x₂₀: int ::
            ((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && old(i) <= i₁₉
                    && i₁₉ < i)
               ==> (exists i₁₉: int ::
                      i₁₉ < 59
                      && x₂₀ == i₁₉
                      && old(i) <= i₁₉
                      && i₁₉ < i
                      && x[x₂₀] == old(x)[1 + i₁₉])))
      && (forall x₂₀: int ::
            (!((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && old(i) <= i₁₉
                    && i₁₉ < i)
            )
               ==> x[x₂₀] == old(x[x₂₀])))
      && (forall i₁₉: int ::
            (  old(i) <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < 59));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[60 - 1 := temp];
  var avg₇: int;
  avg₇ := call avg(x);
  ret5 := avg₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

