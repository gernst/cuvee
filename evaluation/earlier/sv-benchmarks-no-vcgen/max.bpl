data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure max(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < N));
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
  modifies N;
{
  havoc N;
  if(1 < N) {
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
        while(i < N)
          decreases N - i;
          invariant true
            && 0 <= i
            && i <= N
            && (forall i₂₀: int ::
                  (  0 <= i₂₀
                    && i₂₀ < i
                     ==> i₂₀ < N));
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
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₂₅: int ::
                  i₂₅ < N);
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
    while(i < N - 1)
      decreases N - 1 - i;
      invariant true
        && i <= -1 + N
        && (forall x₂₇: int ::
              ((exists i₂₆: int ::
                    x₂₇ == i₂₆)
                 ==> (exists i₂₆: int ::
                        i₂₆ < -1 + N
                        && x₂₇ == i₂₆
                        && x[x₂₇] == old(x)[1 + i₂₆])))
        && (forall x₂₇: int ::
              (!((exists i₂₆: int ::
                    x₂₇ == i₂₆)
              )
                 ==> x[x₂₇] == old(x[x₂₇])))
        && (forall i₂₆: int ::
              i₂₆ < -1 + N);
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var max₆: int;
    {
      var x: [int]int := x;
      havoc max₆;
      {
        var i: int;
        var ret: int;
        ret := 0;
        i := 0;
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₃₀: int ::
                  i₃₀ < N);
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
  }
  c#result := 1;
  return;
}

