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
  while(i < 20)
    decreases 20 - i;
    invariant true
      && old(i) <= i
      && i <= 20
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
               ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                      i₃ < 20
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
               ==> i₃ < 20));
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
  while(i < 20)
    decreases 20 - i;
    invariant true
      && old(cnt) <= cnt
      && old(i) <= i
      && i <= 20
      && (forall cnt₁₀: int, i₁₁: int ::
            (  old(cnt₁₀) <= cnt₁₀
              && old(i₁₁) <= i₁₁
              && old(cnt) <= cnt₁₀
              && cnt₁₀ < cnt
              && old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 20));
  {
    if(20 / 2 < i) {
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
  while(i < 20 - 1)
    decreases 20 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 19
      && (forall x₂₄: int ::
            ((exists i₂₃: int ::
                    x₂₄ == i₂₃
                    && old(i) <= i₂₃
                    && i₂₃ < i)
               ==> (exists i₂₃: int ::
                      i₂₃ < 19
                      && x₂₄ == i₂₃
                      && old(i) <= i₂₃
                      && i₂₃ < i
                      && x[x₂₄] == old(x)[1 + i₂₃])))
      && (forall x₂₄: int ::
            (!((exists i₂₃: int ::
                    x₂₄ == i₂₃
                    && old(i) <= i₂₃
                    && i₂₃ < i)
            )
               ==> x[x₂₄] == old(x[x₂₄])))
      && (forall i₂₃: int ::
            (  old(i₂₃) <= i₂₃
              && old(i) <= i₂₃
              && i₂₃ < i
               ==> i₂₃ < 19));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var rangesum₈: int;
  rangesum₈ := call rangesum(x);
  ret5 := rangesum₈;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

