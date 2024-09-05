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
  while(i < 40)
    decreases 40 - i;
    invariant true
      && old(i) <= i
      && i <= 40
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < 40));
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
  var i: int := 0;
  while(i < 40)
    decreases 40 - i;
    invariant true
      && old(i) <= i
      && i <= 40
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
               ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                      i₁₄ < 40
                      && x₁₅ == i₁₄
                      && old(i) <= i₁₄
                      && i₁₄ < i
                      && x[x₁₅] == __VERIFIER_nondet_int₃₁₃)))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
            )
               ==> x[x₁₅] == old(x[x₁₅])))
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 40));
  {
    var __VERIFIER_nondet_int₃: int;
    x := x[i := __VERIFIER_nondet_int₃];
    i := i + 1;
  }
  var max₅: int;
  max₅ := call max(x);
  ret := max₅;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₆: int;
  max₆ := call max(x);
  ret2 := max₆;
  temp := x[0];
  var i: int := 0;
  while(i < 40 - 1)
    decreases 40 - 1 - i;
    invariant true
      && old(i) <= i
      && i <= 39
      && (forall x₂₁: int ::
            ((exists i₂₀: int ::
                    x₂₁ == i₂₀
                    && old(i) <= i₂₀
                    && i₂₀ < i)
               ==> (exists i₂₀: int ::
                      i₂₀ < 39
                      && x₂₁ == i₂₀
                      && old(i) <= i₂₀
                      && i₂₀ < i
                      && x[x₂₁] == old(x)[1 + i₂₀])))
      && (forall x₂₁: int ::
            (!((exists i₂₀: int ::
                    x₂₁ == i₂₀
                    && old(i) <= i₂₀
                    && i₂₀ < i)
            )
               ==> x[x₂₁] == old(x[x₂₁])))
      && (forall i₂₀: int ::
            (  old(i) <= i₂₀
              && i₂₀ < i
               ==> i₂₀ < 39));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var max₈: int;
  max₈ := call max(x);
  ret5 := max₈;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

