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
    invariant old(i) <= i
      && (forall ret₄: int, i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> ret₄ < x[i₅]
                  && i₅ < N
                ||   !(ret₄ < x[i₅]
                  )
                  && i₅ < N));
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
    max₃ := call max(x);
    ret := max₃;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var max₄: int;
    max₄ := call max(x);
    ret2 := max₄;
    temp := x[0];
    var i: int := 0;
    while(i < N - 1)
      decreases N - 1 - i;
      invariant old(i) <= i
        && (forall i₂₀: int ::
              (  old(i) <= i₂₀
                && i₂₀ < i
                 ==> i₂₀ < -1 + N
                  && x[i₂₀] == old(x)[1 + i₂₀]))
        && (forall i₂₀: int ::
              (!(  old(i) <= i₂₀
                && i₂₀ < i
              )
                 ==> x[i₂₀] == old(x)[i₂₀]));
    {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var max₆: int;
    max₆ := call max(x);
    ret5 := max₆;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

