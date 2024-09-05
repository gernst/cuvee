data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure bAnd(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < N));
  {
    res := c#bitand(res, x[i]);
    i := i + 1;
  }
  c#result := res;
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
      invariant true
        && old(i) <= i
        && i <= N
        && (forall x₁₅: int ::
              ((exists i₁₄: int ::
                      x₁₅ == i₁₄
                      && old(i) <= i₁₄
                      && i₁₄ < i)
                 ==> (exists __VERIFIER_nondet_int₂₁₃: int, i₁₄: int ::
                        i₁₄ < N
                        && x₁₅ == i₁₄
                        && old(i) <= i₁₄
                        && i₁₄ < i
                        && x[x₁₅] == __VERIFIER_nondet_int₂₁₃)))
        && (forall x₁₅: int ::
              (!((exists i₁₄: int ::
                      x₁₅ == i₁₄
                      && old(i) <= i₁₄
                      && i₁₄ < i)
              )
                 ==> x[x₁₅] == old(x[x₁₅])))
        && (forall i₁₄: int ::
              (  old(i) <= i₁₄
                && i₁₄ < i
                 ==> i₁₄ < N));
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
    while(i < N - 1)
      decreases N - 1 - i;
      invariant true
        && old(i) <= i
        && i <= -1 + N
        && (forall x₂₅: int ::
              ((exists i₂₄: int ::
                      x₂₅ == i₂₄
                      && old(i) <= i₂₄
                      && i₂₄ < i)
                 ==> (exists i₂₄: int ::
                        i₂₄ < -1 + N
                        && x₂₅ == i₂₄
                        && old(i) <= i₂₄
                        && i₂₄ < i
                        && x[x₂₅] == old(x)[1 + i₂₄])))
        && (forall x₂₅: int ::
              (!((exists i₂₄: int ::
                      x₂₅ == i₂₄
                      && old(i) <= i₂₄
                      && i₂₄ < i)
              )
                 ==> x[x₂₅] == old(x[x₂₅])))
        && (forall i₂₄: int ::
              (  old(i) <= i₂₄
                && i₂₄ < i
                 ==> i₂₄ < -1 + N));
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var bAnd₇: int;
    bAnd₇ := call bAnd(x);
    ret5 := bAnd₇;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

