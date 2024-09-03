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
  while(i < 10000)
    decreases 10000 - i;
    invariant true
      && 1 <= i
      && i <= 10000
      && (forall i₄: int ::
            (  1 <= i₄
              && i₄ < i
               ==> i₄ < 10000));
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
  while(i < 10000)
    decreases 10000 - i;
    invariant true
      && 0 <= i
      && i <= 10000
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && 0 <= i₁₃
                    && i₁₃ < i)
               ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                      i₁₃ < 10000
                      && x₁₄ == i₁₃
                      && 0 <= i₁₃
                      && i₁₃ < i
                      && x[x₁₄] == __VERIFIER_nondet_int₂₁₂)))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && 0 <= i₁₃
                    && i₁₃ < i)
            )
               ==> x[x₁₄] == old(x[x₁₄])))
      && (forall i₁₃: int ::
            (  0 <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 10000));
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
      while(i < 10000)
        decreases 10000 - i;
        invariant true
          && 1 <= i
          && i <= 10000
          && (forall i₂₂: int ::
                (  1 <= i₂₂
                  && i₂₂ < i
                   ==> i₂₂ < 10000));
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
      while(i < 10000)
        decreases 10000 - i;
        invariant true
          && i <= 10000
          && (forall i₂₆: int ::
                i₂₆ < 10000);
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
  while(i < 10000 - 1)
    decreases 10000 - 1 - i;
    invariant true
      && i <= 9999
      && (forall x₂₈: int ::
            ((exists i₂₇: int ::
                  x₂₈ == i₂₇)
               ==> (exists i₂₇: int ::
                      i₂₇ < 9999
                      && x₂₈ == i₂₇
                      && x[x₂₈] == old(x)[1 + i₂₇])))
      && (forall x₂₈: int ::
            (!((exists i₂₇: int ::
                  x₂₈ == i₂₇)
            )
               ==> x[x₂₈] == old(x[x₂₈])))
      && (forall i₂₇: int ::
            i₂₇ < 9999);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[10000 - 1 := temp];
  var bAnd₇: int;
  {
    var x: [int]int := x;
    havoc bAnd₇;
    {
      var i: int;
      var res: int;
      res := x[0];
      i := 1;
      while(i < 10000)
        decreases 10000 - i;
        invariant true
          && i <= 10000
          && (forall i₃₀: int ::
                i₃₀ < 10000);
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
  c#result := 1;
  return;
}

