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
  while(i < 20)
    decreases 20 - i;
    invariant true
      && old(i) <= i
      && i <= 20
      && (forall i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> i₂ < 20));
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
  var i: int := 0;
  while(i < 20)
    decreases 20 - i;
    invariant true
      && old(i) <= i
      && i <= 20
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
               ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                      i₁₁ < 20
                      && x₁₂ == i₁₁
                      && old(i) <= i₁₁
                      && i₁₁ < i
                      && x[x₁₂] == __VERIFIER_nondet_int₄₁₀)))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
            )
               ==> x[x₁₂] == old(x[x₁₂])))
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 20));
  {
    var __VERIFIER_nondet_int₄: int;
    x := x[i := __VERIFIER_nondet_int₄];
    i := i + 1;
  }
  var sep₆: int;
  sep₆ := call sep(x);
  ret := sep₆;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₇: int;
  sep₇ := call sep(x);
  ret2 := sep₇;
  temp := x[0];
  var i: int := 0;
  while(i < 20 - 1)
    decreases 20 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 19
      && (forall x₁₈: int ::
            ((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
               ==> (exists i₁₇: int ::
                      i₁₇ < 19
                      && x₁₈ == i₁₇
                      && old(i) <= i₁₇
                      && i₁₇ < i
                      && x[x₁₈] == old(x)[1 + i₁₇])))
      && (forall x₁₈: int ::
            (!((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
            )
               ==> x[x₁₈] == old(x[x₁₈])))
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 19));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var sep₉: int;
  sep₉ := call sep(x);
  ret5 := sep₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

