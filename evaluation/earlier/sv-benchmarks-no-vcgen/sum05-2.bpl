data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sum(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 5)
    decreases 5 - i;
    invariant true
      && 0 <= i
      && i <= 5
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ < 5));
  {
    ret := ret + x[i];
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
  while(i < 5)
    decreases 5 - i;
    invariant true
      && 0 <= i
      && i <= 5
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && 0 <= i₁₃
                    && i₁₃ < i)
               ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                      i₁₃ < 5
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
               ==> i₁₃ < 5));
  {
    var __VERIFIER_nondet_int₂: int;
    x := x[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var sum₄: int;
  {
    var x: [int]int := x;
    havoc sum₄;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && 0 <= i
          && i <= 5
          && (forall i₂₂: int ::
                (  0 <= i₂₂
                  && i₂₂ < i
                   ==> i₂₂ < 5));
      {
        ret := ret + x[i];
        i := i + 1;
      }
      sum₄ := ret;
      return;
    }
  }
  ret := sum₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sum₅: int;
  {
    var x: [int]int := x;
    havoc sum₅;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && i <= 5
          && (forall i₂₆: int ::
                i₂₆ < 5);
      {
        ret := ret + x[i];
        i := i + 1;
      }
      sum₅ := ret;
      return;
    }
  }
  ret2 := sum₅;
  temp := x[0];
  var i: int := 0;
  while(i < 5 - 1)
    decreases 5 - 1 - i;
    invariant true
      && i <= 4
      && (forall x₂₈: int ::
            ((exists i₂₇: int ::
                  x₂₈ == i₂₇)
               ==> (exists i₂₇: int ::
                      i₂₇ < 4
                      && x₂₈ == i₂₇
                      && x[x₂₈] == old(x)[1 + i₂₇])))
      && (forall x₂₈: int ::
            (!((exists i₂₇: int ::
                  x₂₈ == i₂₇)
            )
               ==> x[x₂₈] == old(x[x₂₈])))
      && (forall i₂₇: int ::
            i₂₇ < 4);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var sum₇: int;
  {
    var x: [int]int := x;
    havoc sum₇;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && i <= 5
          && (forall i₃₀: int ::
                i₃₀ < 5);
      {
        ret := ret + x[i];
        i := i + 1;
      }
      sum₇ := ret;
      return;
    }
  }
  ret5 := sum₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

