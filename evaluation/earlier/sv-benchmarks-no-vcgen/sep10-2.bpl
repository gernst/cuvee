data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sep(x: [int]int)
  returns (c#result: int)
{
  var ret: int := 0;
  var i: int := 0;
  while(i < 10)
    decreases 10 - i;
    invariant true
      && 0 <= i
      && i <= 10
      && (forall i₂: int ::
            (  0 <= i₂
              && i₂ < i
               ==> i₂ < 10));
  {
    if(x[i] % 2 == 0) {
      ret := ret + 1;
    } else {
      ret := ret - 1;
    }
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
  while(i < 10)
    decreases 10 - i;
    invariant true
      && 0 <= i
      && i <= 10
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && 0 <= i₁₁
                    && i₁₁ < i)
               ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                      i₁₁ < 10
                      && x₁₂ == i₁₁
                      && 0 <= i₁₁
                      && i₁₁ < i
                      && x[x₁₂] == __VERIFIER_nondet_int₄₁₀)))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && 0 <= i₁₁
                    && i₁₁ < i)
            )
               ==> x[x₁₂] == old(x[x₁₂])))
      && (forall i₁₁: int ::
            (  0 <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 10));
  {
    var __VERIFIER_nondet_int₄: int;
    x := x[i := __VERIFIER_nondet_int₄];
    i := i + 1;
  }
  var sep₆: int;
  {
    var x: [int]int := x;
    havoc sep₆;
    {
      var ret: int := 0;
      var i: int := 0;
      while(i < 10)
        decreases 10 - i;
        invariant true
          && 0 <= i
          && i <= 10
          && (forall i₁₈: int ::
                (  0 <= i₁₈
                  && i₁₈ < i
                   ==> i₁₈ < 10));
      {
        if(x[i] % 2 == 0) {
          ret := ret + 1;
        } else {
          ret := ret - 1;
        }
        i := i + 1;
      }
      sep₆ := ret;
      return;
    }
  }
  ret := sep₆;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₇: int;
  {
    var x: [int]int := x;
    havoc sep₇;
    {
      var ret: int := 0;
      var i: int := 0;
      while(i < 10)
        decreases 10 - i;
        invariant true
          && i <= 10
          && (forall i₂₂: int ::
                i₂₂ < 10);
      {
        if(x[i] % 2 == 0) {
          ret := ret + 1;
        } else {
          ret := ret - 1;
        }
        i := i + 1;
      }
      sep₇ := ret;
      return;
    }
  }
  ret2 := sep₇;
  temp := x[0];
  var i: int := 0;
  while(i < 10 - 1)
    decreases 10 - 1 - i;
    invariant true
      && i <= 9
      && (forall x₂₄: int ::
            ((exists i₂₃: int ::
                  x₂₄ == i₂₃)
               ==> (exists i₂₃: int ::
                      i₂₃ < 9
                      && x₂₄ == i₂₃
                      && x[x₂₄] == old(x)[1 + i₂₃])))
      && (forall x₂₄: int ::
            (!((exists i₂₃: int ::
                  x₂₄ == i₂₃)
            )
               ==> x[x₂₄] == old(x[x₂₄])))
      && (forall i₂₃: int ::
            i₂₃ < 9);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[10 - 1 := temp];
  var sep₉: int;
  {
    var x: [int]int := x;
    havoc sep₉;
    {
      var ret: int := 0;
      var i: int := 0;
      while(i < 10)
        decreases 10 - i;
        invariant true
          && i <= 10
          && (forall i₂₆: int ::
                i₂₆ < 10);
      {
        if(x[i] % 2 == 0) {
          ret := ret + 1;
        } else {
          ret := ret - 1;
        }
        i := i + 1;
      }
      sep₉ := ret;
      return;
    }
  }
  ret5 := sep₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

