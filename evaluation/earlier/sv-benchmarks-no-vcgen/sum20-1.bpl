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
  while(i < 20)
    decreases 20 - i;
    invariant true
      && 0 <= i
      && i <= 20
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ < 20));
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
  var sum₂: int;
  {
    var x: [int]int := x;
    havoc sum₂;
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
          && (forall i₁₇: int ::
                (  0 <= i₁₇
                  && i₁₇ < i
                   ==> i₁₇ < 20));
      {
        ret := ret + x[i];
        i := i + 1;
      }
      sum₂ := ret;
      return;
    }
  }
  ret := sum₂;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sum₃: int;
  {
    var x: [int]int := x;
    havoc sum₃;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 20)
        decreases 20 - i;
        invariant true
          && i <= 20
          && (forall i₂₁: int ::
                i₂₁ < 20);
      {
        ret := ret + x[i];
        i := i + 1;
      }
      sum₃ := ret;
      return;
    }
  }
  ret2 := sum₃;
  temp := x[0];
  var i: int := 0;
  while(i < 20 - 1)
    decreases 20 - 1 - i;
    invariant true
      && i <= 19
      && (forall x₂₃: int ::
            ((exists i₂₂: int ::
                  x₂₃ == i₂₂)
               ==> (exists i₂₂: int ::
                      i₂₂ < 19
                      && x₂₃ == i₂₂
                      && x[x₂₃] == old(x)[1 + i₂₂])))
      && (forall x₂₃: int ::
            (!((exists i₂₂: int ::
                  x₂₃ == i₂₂)
            )
               ==> x[x₂₃] == old(x[x₂₃])))
      && (forall i₂₂: int ::
            i₂₂ < 19);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var sum₅: int;
  {
    var x: [int]int := x;
    havoc sum₅;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 20)
        decreases 20 - i;
        invariant true
          && i <= 20
          && (forall i₂₅: int ::
                i₂₅ < 20);
      {
        ret := ret + x[i];
        i := i + 1;
      }
      sum₅ := ret;
      return;
    }
  }
  ret5 := sum₅;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

