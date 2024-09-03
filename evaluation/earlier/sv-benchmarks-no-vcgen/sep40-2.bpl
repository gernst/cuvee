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
  while(i < 40)
    decreases 40 - i;
    invariant true
      && 0 <= i
      && i <= 40
      && (forall i₂: int ::
            (  0 <= i₂
              && i₂ < i
               ==> i₂ < 40));
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
  var sep₄: int;
  {
    var x: [int]int := x;
    havoc sep₄;
    {
      var ret: int := 0;
      var i: int := 0;
      while(i < 40)
        decreases 40 - i;
        invariant true
          && 0 <= i
          && i <= 40
          && (forall i₁₃: int ::
                (  0 <= i₁₃
                  && i₁₃ < i
                   ==> i₁₃ < 40));
      {
        if(x[i] % 2 == 0) {
          ret := ret + 1;
        } else {
          ret := ret - 1;
        }
        i := i + 1;
      }
      sep₄ := ret;
      return;
    }
  }
  ret := sep₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₅: int;
  {
    var x: [int]int := x;
    havoc sep₅;
    {
      var ret: int := 0;
      var i: int := 0;
      while(i < 40)
        decreases 40 - i;
        invariant true
          && i <= 40
          && (forall i₁₇: int ::
                i₁₇ < 40);
      {
        if(x[i] % 2 == 0) {
          ret := ret + 1;
        } else {
          ret := ret - 1;
        }
        i := i + 1;
      }
      sep₅ := ret;
      return;
    }
  }
  ret2 := sep₅;
  temp := x[0];
  var i: int := 0;
  while(i < 40 - 1)
    decreases 40 - 1 - i;
    invariant true
      && i <= 39
      && (forall x₁₉: int ::
            ((exists i₁₈: int ::
                  x₁₉ == i₁₈)
               ==> (exists i₁₈: int ::
                      i₁₈ < 39
                      && x₁₉ == i₁₈
                      && x[x₁₉] == old(x)[1 + i₁₈])))
      && (forall x₁₉: int ::
            (!((exists i₁₈: int ::
                  x₁₉ == i₁₈)
            )
               ==> x[x₁₉] == old(x[x₁₉])))
      && (forall i₁₈: int ::
            i₁₈ < 39);
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var sep₇: int;
  {
    var x: [int]int := x;
    havoc sep₇;
    {
      var ret: int := 0;
      var i: int := 0;
      while(i < 40)
        decreases 40 - i;
        invariant true
          && i <= 40
          && (forall i₂₁: int ::
                i₂₁ < 40);
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
  ret5 := sep₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

