data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure sum(x: [int]int)
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
      && old(i) <= i
      && i <= N
      && (forall i₄: int ::
            (  old(i₄) <= i₄
              && old(i) <= i₄
              && i₄ < i
               ==> i₄ < N));
  {
    ret := ret + x[i];
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
    var sum₂: int;
    sum₂ := call sum(x);
    ret := sum₂;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var sum₃: int;
    sum₃ := call sum(x);
    ret2 := sum₃;
    temp := x[0];
    var i: int := 0;
    while(i < N - 1)
      decreases N - 1 - i;
      invariant true
        && old(i) <= i
        && i <= -1 + N
        && (forall x₂₀: int ::
              ((exists i₁₉: int ::
                      x₂₀ == i₁₉
                      && old(i) <= i₁₉
                      && i₁₉ < i)
                 ==> (exists i₁₉: int ::
                        i₁₉ < -1 + N
                        && x₂₀ == i₁₉
                        && old(i) <= i₁₉
                        && i₁₉ < i
                        && x[x₂₀] == old(x)[1 + i₁₉])))
        && (forall x₂₀: int ::
              (!((exists i₁₉: int ::
                      x₂₀ == i₁₉
                      && old(i) <= i₁₉
                      && i₁₉ < i)
              )
                 ==> x[x₂₀] == old(x[x₂₀])))
        && (forall i₁₉: int ::
              (  old(i₁₉) <= i₁₉
                && old(i) <= i₁₉
                && i₁₉ < i
                 ==> i₁₉ < -1 + N));
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var sum₅: int;
    sum₅ := call sum(x);
    ret5 := sum₅;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

