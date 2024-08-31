data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure bor(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < 10000)
    decreases 10000 - i;
    invariant true
      && old(i) <= i
      && i <= 10000
      && (forall i₄: int ::
            (  old(i₄) <= i₄
              && old(i) <= i₄
              && i₄ < i
               ==> i₄ < 10000));
  {
    res := c#bitor(res, x[i]);
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
  while(i < 10000)
    decreases 10000 - i;
    invariant true
      && old(i) <= i
      && i <= 10000
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
               ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                      i₁₃ < 10000
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
            (  old(i₁₃) <= i₁₃
              && old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 10000));
  {
    var __VERIFIER_nondet_int₂: int;
    x := x[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var bor₄: int;
  bor₄ := call bor(x);
  ret := bor₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bor₅: int;
  bor₅ := call bor(x);
  ret2 := bor₅;
  temp := x[0];
  var i: int := 0;
  while(i < 10000 - 1)
    decreases 10000 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 9999
      && (forall x₂₀: int ::
            ((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && old(i) <= i₁₉
                    && i₁₉ < i)
               ==> (exists i₁₉: int ::
                      i₁₉ < 9999
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
            (  old(i₁₉) <= i₁₉
              && old(i) <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < 9999));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[10000 - 1 := temp];
  var bor₇: int;
  bor₇ := call bor(x);
  ret5 := bor₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

