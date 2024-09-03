data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure avg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 40)
    decreases 40 - i;
    invariant true
      && 0 <= i
      && i <= 40
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ < 40));
  {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret / 40;
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
  var avg₂: int;
  {
    var x: [int]int := x;
    havoc avg₂;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 40)
        decreases 40 - i;
        invariant true
          && 0 <= i
          && i <= 40
          && (forall i₁₇: int ::
                (  0 <= i₁₇
                  && i₁₇ < i
                   ==> i₁₇ < 40));
      {
        ret := ret + x[i];
        i := i + 1;
      }
      avg₂ := ret / 40;
      return;
    }
  }
  ret := avg₂;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₃: int;
  {
    var x: [int]int := x;
    havoc avg₃;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 40)
        decreases 40 - i;
        invariant true
          && i <= 40
          && (forall i₂₁: int ::
                i₂₁ < 40);
      {
        ret := ret + x[i];
        i := i + 1;
      }
      avg₃ := ret / 40;
      return;
    }
  }
  ret2 := avg₃;
  temp := x[0];
  var i: int := 0;
  while(i < 40 - 1)
    decreases 40 - 1 - i;
    invariant true
      && i <= 39
      && (forall x₂₃: int ::
            ((exists i₂₂: int ::
                  x₂₃ == i₂₂)
               ==> (exists i₂₂: int ::
                      i₂₂ < 39
                      && x₂₃ == i₂₂
                      && x[x₂₃] == old(x)[1 + i₂₂])))
      && (forall x₂₃: int ::
            (!((exists i₂₂: int ::
                  x₂₃ == i₂₂)
            )
               ==> x[x₂₃] == old(x[x₂₃])))
      && (forall i₂₂: int ::
            i₂₂ < 39);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var avg₅: int;
  {
    var x: [int]int := x;
    havoc avg₅;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 40)
        decreases 40 - i;
        invariant true
          && i <= 40
          && (forall i₂₅: int ::
                i₂₅ < 40);
      {
        ret := ret + x[i];
        i := i + 1;
      }
      avg₅ := ret / 40;
      return;
    }
  }
  ret5 := avg₅;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

