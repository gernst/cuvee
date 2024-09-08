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
  while(i < 60)
    decreases 60 - i;
    invariant old(i) <= i
      && i <= 60
      && (forall ret₄: int, i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> ret₄ < x[i₅]
                  && i₅ < 60
                ||   !(ret₄ < x[i₅]
                  )
                  && i₅ < 60));
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
  while(i < 60)
    decreases 60 - i;
    invariant old(i) <= i
      && i <= 60
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> (exists __VERIFIER_nondet_int₃₁₃: int ::
                      i₁₄ < 60
                      && x[i₁₄] == __VERIFIER_nondet_int₃₁₃)))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> x[i₁₄] == old(x)[i₁₄]));
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
  while(i < 60 - 1)
    decreases 60 - 1 - i;
    invariant old(i) <= i
      && i <= 59
      && (forall i₁₉: int ::
            (  old(i) <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < 59
                && x[i₁₉] == old(x)[1 + i₁₉]))
      && (forall i₁₉: int ::
            (!(  old(i) <= i₁₉
              && i₁₉ < i
            )
               ==> x[i₁₉] == old(x)[i₁₉]));
  {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[60 - 1 := temp];
  var max₈: int;
  max₈ := call max(x);
  ret5 := max₈;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

