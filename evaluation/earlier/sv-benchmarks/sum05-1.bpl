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
  while(i < 5)
    decreases 5 - i;
    invariant true
      && old(i) <= i
      && i <= 5
      && (forall i₄: int ::
            (  old(i₄) <= i₄
              && old(i) <= i₄
              && i₄ < i
               ==> i₄ < 5));
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
  while(i < 5 - 1)
    decreases 5 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 4
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
               ==> (exists i₁₄: int ::
                      i₁₄ < 4
                      && x₁₅ == i₁₄
                      && old(i) <= i₁₄
                      && i₁₄ < i
                      && x[x₁₅] == old(x)[1 + i₁₄])))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
            )
               ==> x[x₁₅] == old(x[x₁₅])))
      && (forall i₁₄: int ::
            (  old(i₁₄) <= i₁₄
              && old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 4));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var sum₅: int;
  sum₅ := call sum(x);
  ret5 := sum₅;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

