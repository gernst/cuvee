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
  while(i < 100)
    decreases 100 - i;
    invariant true
      && 1 <= i
      && i <= 100
      && (forall i₄: int ::
            (  1 <= i₄
              && i₄ < i
               ==> i₄ < 100));
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
  while(i < 100)
    decreases 100 - i;
    invariant true
      && 0 <= i
      && i <= 100
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && 0 <= i₁₃
                    && i₁₃ < i)
               ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                      i₁₃ < 100
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
               ==> i₁₃ < 100));
  {
    var __VERIFIER_nondet_int₂: int;
    x := x[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var bor₄: int;
  {
    var x: [int]int := x;
    havoc bor₄;
    {
      var i: int;
      var res: int;
      res := x[0];
      i := 1;
      while(i < 100)
        decreases 100 - i;
        invariant true
          && 1 <= i
          && i <= 100
          && (forall i₂₂: int ::
                (  1 <= i₂₂
                  && i₂₂ < i
                   ==> i₂₂ < 100));
      {
        res := c#bitor(res, x[i]);
        i := i + 1;
      }
      bor₄ := res;
      return;
    }
  }
  ret := bor₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bor₅: int;
  {
    var x: [int]int := x;
    havoc bor₅;
    {
      var i: int;
      var res: int;
      res := x[0];
      i := 1;
      while(i < 100)
        decreases 100 - i;
        invariant true
          && i <= 100
          && (forall i₂₆: int ::
                i₂₆ < 100);
      {
        res := c#bitor(res, x[i]);
        i := i + 1;
      }
      bor₅ := res;
      return;
    }
  }
  ret2 := bor₅;
  temp := x[0];
  var i: int := 0;
  while(i < 100 - 1)
    decreases 100 - 1 - i;
    invariant true
      && i <= 99
      && (forall x₂₈: int ::
            ((exists i₂₇: int ::
                  x₂₈ == i₂₇)
               ==> (exists i₂₇: int ::
                      i₂₇ < 99
                      && x₂₈ == i₂₇
                      && x[x₂₈] == old(x)[1 + i₂₇])))
      && (forall x₂₈: int ::
            (!((exists i₂₇: int ::
                  x₂₈ == i₂₇)
            )
               ==> x[x₂₈] == old(x[x₂₈])))
      && (forall i₂₇: int ::
            i₂₇ < 99);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[100 - 1 := temp];
  var bor₇: int;
  {
    var x: [int]int := x;
    havoc bor₇;
    {
      var i: int;
      var res: int;
      res := x[0];
      i := 1;
      while(i < 100)
        decreases 100 - i;
        invariant true
          && i <= 100
          && (forall i₃₀: int ::
                i₃₀ < 100);
      {
        res := c#bitor(res, x[i]);
        i := i + 1;
      }
      bor₇ := res;
      return;
    }
  }
  ret5 := bor₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

