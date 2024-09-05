data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure bAnd(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < 100000));
  {
    res := c#bitand(res, x[i]);
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
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
               ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                      i₁₃ < 100000
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
               ==> i₁₃ < 100000));
  {
    var __VERIFIER_nondet_int₂: int;
    x := x[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var bAnd₄: int;
  bAnd₄ := call bAnd(x);
  ret := bAnd₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bAnd₅: int;
  bAnd₅ := call bAnd(x);
  ret2 := bAnd₅;
  temp := x[0];
  var i: int := 0;
  while(i < 100000 - 1)
    decreases 100000 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 99999
      && (forall x₂₀: int ::
            ((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && old(i) <= i₁₉
                    && i₁₉ < i)
               ==> (exists i₁₉: int ::
                      i₁₉ < 99999
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
               ==> i₁₉ < 99999));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[100000 - 1 := temp];
  var bAnd₇: int;
  bAnd₇ := call bAnd(x);
  ret5 := bAnd₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

