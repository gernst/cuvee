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
      && old(i) <= i
      && i <= N
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
               ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                      i₃ < N
                      && x₄ == i₃
                      && old(i) <= i₃
                      && i₃ < i
                      && x[x₄] == __VERIFIER_nondet_int₁₂)))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
            )
               ==> x[x₄] == old(x[x₄])))
      && (forall i₃: int ::
            (  old(i₃) <= i₃
              && old(i) <= i₃
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
      && old(cnt) <= cnt
      && old(i) <= i
      && i <= N
      && (forall cnt₁₀: int, i₁₁: int ::
            (  old(cnt₁₀) <= cnt₁₀
              && old(i₁₁) <= i₁₁
              && old(cnt) <= cnt₁₀
              && cnt₁₀ < cnt
              && old(i) <= i₁₁
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
    init_nondet₄ := call init_nondet(x);
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var rangesum₅: int;
    rangesum₅ := call rangesum(x);
    ret := rangesum₅;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var rangesum₆: int;
    rangesum₆ := call rangesum(x);
    ret2 := rangesum₆;
    temp := x[0];
    var i: int := 0;
    while(i < N - 1)
      decreases N - 1 - i;
      invariant true
        && old(i) <= i
        && i <= -1 + N
        && (forall x₃₁: int ::
              ((exists i₃₀: int ::
                      x₃₁ == i₃₀
                      && old(i) <= i₃₀
                      && i₃₀ < i)
                 ==> (exists i₃₀: int ::
                        i₃₀ < -1 + N
                        && x₃₁ == i₃₀
                        && old(i) <= i₃₀
                        && i₃₀ < i
                        && x[x₃₁] == old(x)[1 + i₃₀])))
        && (forall x₃₁: int ::
              (!((exists i₃₀: int ::
                      x₃₁ == i₃₀
                      && old(i) <= i₃₀
                      && i₃₀ < i)
              )
                 ==> x[x₃₁] == old(x[x₃₁])))
        && (forall i₃₀: int ::
              (  old(i₃₀) <= i₃₀
                && old(i) <= i₃₀
                && i₃₀ < i
                 ==> i₃₀ < -1 + N));
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var rangesum₈: int;
    rangesum₈ := call rangesum(x);
    ret5 := rangesum₈;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

