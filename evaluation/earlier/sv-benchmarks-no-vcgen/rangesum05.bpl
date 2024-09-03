data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure init_nondet(x: [int]int)
  returns (c#result: c#void)
{
  var i: int;
  i := 0;
  while(i < 5)
    decreases 5 - i;
    invariant true
      && 0 <= i
      && i <= 5
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && 0 <= i₃
                    && i₃ < i)
               ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                      i₃ < 5
                      && x₄ == i₃
                      && 0 <= i₃
                      && i₃ < i
                      && x[x₄] == __VERIFIER_nondet_int₁₂)))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && 0 <= i₃
                    && i₃ < i)
            )
               ==> x[x₄] == old(x[x₄])))
      && (forall i₃: int ::
            (  0 <= i₃
              && i₃ < i
               ==> i₃ < 5));
  {
    var __VERIFIER_nondet_int₁: int;
    x := x[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
}

procedure rangesum(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  var cnt: int := 0;
  i := 0;
  while(i < 5)
    decreases 5 - i;
    invariant true
      && 0 <= cnt
      && 0 <= i
      && i <= 5
      && (forall cnt₁₀: int, i₁₁: int ::
            (  0 <= cnt₁₀
              && 0 <= i₁₁
              && cnt₁₀ < cnt
              && i₁₁ < i
               ==> i₁₁ < 5));
  {
    if(5 / 2 < i) {
      ret := ret + x[i];
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  if(cnt != 0) {
    c#result := ret / cnt;
    return;
  } else {
    c#result := 0;
    return;
  }
}

procedure main()
  returns (c#result: int)
{
  var x: [int]int;
  var init_nondet₄: c#void;
  {
    var x: [int]int := x;
    havoc init_nondet₄;
    {
      var i: int;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && 0 <= i
          && i <= 5
          && (forall x₂₁: int ::
                ((exists i₂₀: int ::
                        x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i)
                   ==> (exists __VERIFIER_nondet_int₁₁₉: int, i₂₀: int ::
                          i₂₀ < 5
                          && x₂₁ == i₂₀
                          && 0 <= i₂₀
                          && i₂₀ < i
                          && x[x₂₁] == __VERIFIER_nondet_int₁₁₉)))
          && (forall x₂₁: int ::
                (!((exists i₂₀: int ::
                        x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i)
                )
                   ==> x[x₂₁] == old(x[x₂₁])))
          && (forall i₂₀: int ::
                (  0 <= i₂₀
                  && i₂₀ < i
                   ==> i₂₀ < 5));
      {
        var __VERIFIER_nondet_int₁: int;
        x := x[i := __VERIFIER_nondet_int₁];
        i := i + 1;
      }
    }
  }
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var rangesum₅: int;
  {
    var x: [int]int := x;
    havoc rangesum₅;
    {
      var i: int;
      var ret: int;
      ret := 0;
      var cnt: int := 0;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && 0 <= cnt
          && 0 <= i
          && i <= 5
          && (forall cnt₃₃: int, i₃₄: int ::
                (  0 <= cnt₃₃
                  && 0 <= i₃₄
                  && cnt₃₃ < cnt
                  && i₃₄ < i
                   ==> i₃₄ < 5));
      {
        if(5 / 2 < i) {
          ret := ret + x[i];
          cnt := cnt + 1;
        }
        i := i + 1;
      }
      if(cnt != 0) {
        rangesum₅ := ret / cnt;
        return;
      } else {
        rangesum₅ := 0;
        return;
      }
    }
  }
  ret := rangesum₅;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var rangesum₆: int;
  {
    var x: [int]int := x;
    havoc rangesum₆;
    {
      var i: int;
      var ret: int;
      ret := 0;
      var cnt: int := 0;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && i <= 5
          && (forall i₄₀: int ::
                i₄₀ < 5);
      {
        if(5 / 2 < i) {
          ret := ret + x[i];
          cnt := cnt + 1;
        }
        i := i + 1;
      }
      if(cnt != 0) {
        rangesum₆ := ret / cnt;
        return;
      } else {
        rangesum₆ := 0;
        return;
      }
    }
  }
  ret2 := rangesum₆;
  temp := x[0];
  var i: int := 0;
  while(i < 5 - 1)
    decreases 5 - 1 - i;
    invariant true
      && i <= 4
      && (forall x₄₂: int ::
            ((exists i₄₁: int ::
                  x₄₂ == i₄₁)
               ==> (exists i₄₁: int ::
                      i₄₁ < 4
                      && x₄₂ == i₄₁
                      && x[x₄₂] == old(x)[1 + i₄₁])))
      && (forall x₄₂: int ::
            (!((exists i₄₁: int ::
                  x₄₂ == i₄₁)
            )
               ==> x[x₄₂] == old(x[x₄₂])))
      && (forall i₄₁: int ::
            i₄₁ < 4);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var rangesum₈: int;
  {
    var x: [int]int := x;
    havoc rangesum₈;
    {
      var i: int;
      var ret: int;
      ret := 0;
      var cnt: int := 0;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && i <= 5
          && (forall i₄₅: int ::
                i₄₅ < 5);
      {
        if(5 / 2 < i) {
          ret := ret + x[i];
          cnt := cnt + 1;
        }
        i := i + 1;
      }
      if(cnt != 0) {
        rangesum₈ := ret / cnt;
        return;
      } else {
        rangesum₈ := 0;
        return;
      }
    }
  }
  ret5 := rangesum₈;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

