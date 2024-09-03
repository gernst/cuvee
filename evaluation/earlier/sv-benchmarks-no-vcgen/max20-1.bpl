data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure max(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 20)
    decreases 20 - i;
    invariant true
      && 0 <= i
      && i <= 20
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < 20));
  {
    var x₁: int;
    if(ret < x[i]) {
      x₁ := x[i];
    } else {
      x₁ := ret;
    }
    ret := x₁;
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
  while(i < 20)
    decreases 20 - i;
    invariant true
      && 0 <= i
      && i <= 20
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && 0 <= i₁₄
                    && i₁₄ < i)
               ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                      i₁₄ < 20
                      && x₁₅ == i₁₄
                      && 0 <= i₁₄
                      && i₁₄ < i
                      && x[x₁₅] == __VERIFIER_nondet_int₃₁₃)))
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
               ==> i₁₄ < 20));
  {
    var __VERIFIER_nondet_int₃: int;
    x := x[i := __VERIFIER_nondet_int₃];
    i := i + 1;
  }
  var max₅: int;
  {
    var x: [int]int := x;
    havoc max₅;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 20)
        decreases 20 - i;
        invariant true
          && 0 <= i
          && i <= 20
          && (forall i₂₄: int ::
                (  0 <= i₂₄
                  && i₂₄ < i
                   ==> i₂₄ < 20));
      {
        var x₁: int;
        if(ret < x[i]) {
          x₁ := x[i];
        } else {
          x₁ := ret;
        }
        ret := x₁;
        i := i + 1;
      }
      max₅ := ret;
      return;
    }
  }
  ret := max₅;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₆: int;
  {
    var x: [int]int := x;
    havoc max₆;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 20)
        decreases 20 - i;
        invariant true
          && i <= 20
          && (forall i₂₉: int ::
                i₂₉ < 20);
      {
        var x₁: int;
        if(ret < x[i]) {
          x₁ := x[i];
        } else {
          x₁ := ret;
        }
        ret := x₁;
        i := i + 1;
      }
      max₆ := ret;
      return;
    }
  }
  ret2 := max₆;
  temp := x[0];
  var i: int := 0;
  while(i < 20 - 1)
    decreases 20 - 1 - i;
    invariant true
      && i <= 19
      && (forall x₃₁: int ::
            ((exists i₃₀: int ::
                  x₃₁ == i₃₀)
               ==> (exists i₃₀: int ::
                      i₃₀ < 19
                      && x₃₁ == i₃₀
                      && x[x₃₁] == old(x)[1 + i₃₀])))
      && (forall x₃₁: int ::
            (!((exists i₃₀: int ::
                  x₃₁ == i₃₀)
            )
               ==> x[x₃₁] == old(x[x₃₁])))
      && (forall i₃₀: int ::
            i₃₀ < 19);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var max₈: int;
  {
    var x: [int]int := x;
    havoc max₈;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 20)
        decreases 20 - i;
        invariant true
          && i <= 20
          && (forall i₃₄: int ::
                i₃₄ < 20);
      {
        var x₁: int;
        if(ret < x[i]) {
          x₁ := x[i];
        } else {
          x₁ := ret;
        }
        ret := x₁;
        i := i + 1;
      }
      max₈ := ret;
      return;
    }
  }
  ret5 := max₈;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

