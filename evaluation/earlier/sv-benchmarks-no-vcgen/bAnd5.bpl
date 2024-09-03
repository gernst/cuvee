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
      && 1 <= i
      && i <= N
      && (forall i₄: int ::
            (  1 <= i₄
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
        && 0 <= i
        && i <= N
        && (forall x₁₅: int ::
              ((exists i₁₄: int ::
                      x₁₅ == i₁₄
                      && 0 <= i₁₄
                      && i₁₄ < i)
                 ==> (exists __VERIFIER_nondet_int₂₁₃: int, i₁₄: int ::
                        i₁₄ < N
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i
                        && x[x₁₅] == __VERIFIER_nondet_int₂₁₃)))
        && (forall x₁₅: int ::
              (!((exists i₁₄: int ::
                      x₁₅ == i₁₄
                      && 0 <= i₁₄
                      && i₁₄ < i)
              )
                 ==> x[x₁₅] == old(x[x₁₅])))
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i
                 ==> i₁₄ < N));
    {
      var __VERIFIER_nondet_int₂: int;
      x := x[i := __VERIFIER_nondet_int₂];
      i := i + 1;
    }
    var bAnd₄: int;
    {
      var x: [int]int := x;
      havoc bAnd₄;
      {
        var i: int;
        var res: int;
        res := x[0];
        i := 1;
        while(i < N)
          decreases N - i;
          invariant true
            && 1 <= i
            && i <= N
            && (forall i₂₃: int ::
                  (  1 <= i₂₃
                    && i₂₃ < i
                     ==> i₂₃ < N));
        {
          res := c#bitand(res, x[i]);
          i := i + 1;
        }
        bAnd₄ := res;
        return;
      }
    }
    ret := bAnd₄;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var bAnd₅: int;
    {
      var x: [int]int := x;
      havoc bAnd₅;
      {
        var i: int;
        var res: int;
        res := x[0];
        i := 1;
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₂₇: int ::
                  i₂₇ < N);
        {
          res := c#bitand(res, x[i]);
          i := i + 1;
        }
        bAnd₅ := res;
        return;
      }
    }
    ret2 := bAnd₅;
    temp := x[0];
    var i: int := 0;
    while(i < N - 1)
      decreases N - 1 - i;
      invariant true
        && i <= -1 + N
        && (forall x₂₉: int ::
              ((exists i₂₈: int ::
                    x₂₉ == i₂₈)
                 ==> (exists i₂₈: int ::
                        i₂₈ < -1 + N
                        && x₂₉ == i₂₈
                        && x[x₂₉] == old(x)[1 + i₂₈])))
        && (forall x₂₉: int ::
              (!((exists i₂₈: int ::
                    x₂₉ == i₂₈)
              )
                 ==> x[x₂₉] == old(x[x₂₉])))
        && (forall i₂₈: int ::
              i₂₈ < -1 + N);
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var bAnd₇: int;
    {
      var x: [int]int := x;
      havoc bAnd₇;
      {
        var i: int;
        var res: int;
        res := x[0];
        i := 1;
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₃₁: int ::
                  i₃₁ < N);
        {
          res := c#bitand(res, x[i]);
          i := i + 1;
        }
        bAnd₇ := res;
        return;
      }
    }
    ret5 := bAnd₇;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

