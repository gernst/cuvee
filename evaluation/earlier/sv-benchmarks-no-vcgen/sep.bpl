data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure sep(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var ret: int := 0;
  var i: int := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall i₂: int ::
            (  0 <= i₂
              && i₂ < i
               ==> i₂ < N));
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
  modifies N;
{
  havoc N;
  if(1 < N) {
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
        while(i < N)
          decreases N - i;
          invariant true
            && 0 <= i
            && i <= N
            && (forall i₁₄: int ::
                  (  0 <= i₁₄
                    && i₁₄ < i
                     ==> i₁₄ < N));
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
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₁₈: int ::
                  i₁₈ < N);
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
    while(i < N - 1)
      decreases N - 1 - i;
      invariant true
        && i <= -1 + N
        && (forall x₂₀: int ::
              ((exists i₁₉: int ::
                    x₂₀ == i₁₉)
                 ==> (exists i₁₉: int ::
                        i₁₉ < -1 + N
                        && x₂₀ == i₁₉
                        && x[x₂₀] == old(x)[1 + i₁₉])))
        && (forall x₂₀: int ::
              (!((exists i₁₉: int ::
                    x₂₀ == i₁₉)
              )
                 ==> x[x₂₀] == old(x[x₂₀])))
        && (forall i₁₉: int ::
              i₁₉ < -1 + N);
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var sep₇: int;
    {
      var x: [int]int := x;
      havoc sep₇;
      {
        var ret: int := 0;
        var i: int := 0;
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₂₂: int ::
                  i₂₂ < N);
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
  }
  c#result := 1;
  return;
}

