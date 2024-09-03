data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure init_nondet(x: [int]int)
  returns (c#result: c#void)
  modifies N;
{
  var i: int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && 0 <= i₃
                    && i₃ < i)
               ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                      i₃ < N
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
               ==> i₃ < N));
  {
    var __VERIFIER_nondet_int₁: int;
    x := x[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
}

procedure rangesum(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var i: int;
  var ret: int;
  ret := 0;
  var cnt: int := 0;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= cnt
      && 0 <= i
      && i <= N
      && (forall cnt₁₀: int, i₁₁: int ::
            (  0 <= cnt₁₀
              && 0 <= i₁₁
              && cnt₁₀ < cnt
              && i₁₁ < i
               ==> i₁₁ < N));
  {
    if(N / 2 < i) {
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
  modifies N;
{
  havoc N;
  if(1 < N) {
    var x: [int]int;
    var init_nondet₄: c#void;
    {
      var x: [int]int := x;
      havoc init_nondet₄;
      {
        var i: int;
        i := 0;
        while(i < N)
          decreases N - i;
          invariant true
            && 0 <= i
            && i <= N
            && (forall x₂₂: int ::
                  ((exists i₂₁: int ::
                          x₂₂ == i₂₁
                          && 0 <= i₂₁
                          && i₂₁ < i)
                     ==> (exists __VERIFIER_nondet_int₁₂₀: int, i₂₁: int ::
                            i₂₁ < N
                            && x₂₂ == i₂₁
                            && 0 <= i₂₁
                            && i₂₁ < i
                            && x[x₂₂] == __VERIFIER_nondet_int₁₂₀)))
            && (forall x₂₂: int ::
                  (!((exists i₂₁: int ::
                          x₂₂ == i₂₁
                          && 0 <= i₂₁
                          && i₂₁ < i)
                  )
                     ==> x[x₂₂] == old(x[x₂₂])))
            && (forall i₂₁: int ::
                  (  0 <= i₂₁
                    && i₂₁ < i
                     ==> i₂₁ < N));
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
        while(i < N)
          decreases N - i;
          invariant true
            && 0 <= cnt
            && 0 <= i
            && i <= N
            && (forall cnt₃₄: int, i₃₅: int ::
                  (  0 <= cnt₃₄
                    && 0 <= i₃₅
                    && cnt₃₄ < cnt
                    && i₃₅ < i
                     ==> i₃₅ < N));
        {
          if(N / 2 < i) {
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
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₄₁: int ::
                  i₄₁ < N);
        {
          if(N / 2 < i) {
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
    while(i < N - 1)
      decreases N - 1 - i;
      invariant true
        && i <= -1 + N
        && (forall x₄₃: int ::
              ((exists i₄₂: int ::
                    x₄₃ == i₄₂)
                 ==> (exists i₄₂: int ::
                        i₄₂ < -1 + N
                        && x₄₃ == i₄₂
                        && x[x₄₃] == old(x)[1 + i₄₂])))
        && (forall x₄₃: int ::
              (!((exists i₄₂: int ::
                    x₄₃ == i₄₂)
              )
                 ==> x[x₄₃] == old(x[x₄₃])))
        && (forall i₄₂: int ::
              i₄₂ < -1 + N);
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
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
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₄₆: int ::
                  i₄₆ < N);
        {
          if(N / 2 < i) {
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
  }
  c#result := 1;
  return;
}

