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
  while(i < 5)
    decreases 5 - i;
    invariant true
      && 0 <= i
      && i <= 5
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < 5));
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
  var max₃: int;
  {
    var x: [int]int := x;
    havoc max₃;
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
          && (forall i₁₉: int ::
                (  0 <= i₁₉
                  && i₁₉ < i
                   ==> i₁₉ < 5));
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
      max₃ := ret;
      return;
    }
  }
  ret := max₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₄: int;
  {
    var x: [int]int := x;
    havoc max₄;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && i <= 5
          && (forall i₂₄: int ::
                i₂₄ < 5);
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
      max₄ := ret;
      return;
    }
  }
  ret2 := max₄;
  temp := x[0];
  var i: int := 0;
  while(i < 5 - 1)
    decreases 5 - 1 - i;
    invariant true
      && i <= 4
      && (forall x₂₆: int ::
            ((exists i₂₅: int ::
                  x₂₆ == i₂₅)
               ==> (exists i₂₅: int ::
                      i₂₅ < 4
                      && x₂₆ == i₂₅
                      && x[x₂₆] == old(x)[1 + i₂₅])))
      && (forall x₂₆: int ::
            (!((exists i₂₅: int ::
                  x₂₆ == i₂₅)
            )
               ==> x[x₂₆] == old(x[x₂₆])))
      && (forall i₂₅: int ::
            i₂₅ < 4);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var max₆: int;
  {
    var x: [int]int := x;
    havoc max₆;
    {
      var i: int;
      var ret: int;
      ret := 0;
      i := 0;
      while(i < 5)
        decreases 5 - i;
        invariant true
          && i <= 5
          && (forall i₂₉: int ::
                i₂₉ < 5);
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
  ret5 := max₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

