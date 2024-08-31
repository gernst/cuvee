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
      && old(i) <= i
      && i <= 20
      && (forall i₅: int ::
            (  old(i₅) <= i₅
              && old(i) <= i₅
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
  while(i < 20 - 1)
    decreases 20 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 19
      && (forall x₁₆: int ::
            ((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
               ==> (exists i₁₅: int ::
                      i₁₅ < 19
                      && x₁₆ == i₁₅
                      && old(i) <= i₁₅
                      && i₁₅ < i
                      && x[x₁₆] == old(x)[1 + i₁₅])))
      && (forall x₁₆: int ::
            (!((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
            )
               ==> x[x₁₆] == old(x[x₁₆])))
      && (forall i₁₅: int ::
            (  old(i₁₅) <= i₁₅
              && old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < 19));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var max₆: int;
  max₆ := call max(x);
  ret5 := max₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

