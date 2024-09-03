data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure avg(x: [int]int)
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
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ < N));
  {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret / N;
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
    var avg₂: int;
    {
      var x: [int]int := x;
      havoc avg₂;
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
            && (forall i₁₈: int ::
                  (  0 <= i₁₈
                    && i₁₈ < i
                     ==> i₁₈ < N));
        {
          ret := ret + x[i];
          i := i + 1;
        }
        avg₂ := ret / N;
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
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₂₂: int ::
                  i₂₂ < N);
        {
          ret := ret + x[i];
          i := i + 1;
        }
        avg₃ := ret / N;
        return;
      }
    }
    ret2 := avg₃;
    temp := x[0];
    var i: int := 0;
    while(i < N - 1)
      decreases N - 1 - i;
      invariant true
        && i <= -1 + N
        && (forall x₂₄: int ::
              ((exists i₂₃: int ::
                    x₂₄ == i₂₃)
                 ==> (exists i₂₃: int ::
                        i₂₃ < -1 + N
                        && x₂₄ == i₂₃
                        && x[x₂₄] == old(x)[1 + i₂₃])))
        && (forall x₂₄: int ::
              (!((exists i₂₃: int ::
                    x₂₄ == i₂₃)
              )
                 ==> x[x₂₄] == old(x[x₂₄])))
        && (forall i₂₃: int ::
              i₂₃ < -1 + N);
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var avg₅: int;
    {
      var x: [int]int := x;
      havoc avg₅;
      {
        var i: int;
        var ret: int;
        ret := 0;
        i := 0;
        while(i < N)
          decreases N - i;
          invariant true
            && i <= N
            && (forall i₂₆: int ::
                  i₂₆ < N);
        {
          ret := ret + x[i];
          i := i + 1;
        }
        avg₅ := ret / N;
        return;
      }
    }
    ret5 := avg₅;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

