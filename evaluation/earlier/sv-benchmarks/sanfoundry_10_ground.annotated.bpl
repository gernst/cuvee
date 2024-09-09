data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var n: int := 100000;
  var pos: int;
  var __VERIFIER_nondet_int₁: int;
  var element: int;
  element := __VERIFIER_nondet_int₁;
  var found: int := 0;
  var vectorx: [int]int;
  i := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> (exists __VERIFIER_nondet_int₂₆: int ::
                      i₇ < n
                      && vectorx[i₇] == __VERIFIER_nondet_int₂₆)))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> vectorx[i₇] == old(vectorx)[i₇]));
  {
    var __VERIFIER_nondet_int₂: int;
    vectorx := vectorx[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < n && !(found != 0))
    decreases n - i;
    invariant old(i) <= i
      && (forall found₁₀: int, i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> vectorx[i₁₂] == element
                  && i₁₂ < n
                  && found₁₀ == 0
                ||   vectorx[i₁₂] != element
                  && i₁₂ < n
                  && found₁₀ == 0));
  {
    if(vectorx[i] == element) {
      found := 1;
      pos := i;
    }
    i := i + 1;
  }
  if(found != 0) {
    i := pos;
    while(i < n - 1)
      decreases n - 1 - i;
      invariant old(i) <= i
        && (forall i₁₆: int ::
              (  old(i) <= i₁₆
                && i₁₆ < i
                 ==> i₁₆ < -1 + n
                  && vectorx[i₁₆] == old(vectorx)[1 + i₁₆]))
        && (forall i₁₆: int ::
              (!(  old(i) <= i₁₆
                && i₁₆ < i
              )
                 ==> vectorx[i₁₆] == old(vectorx)[i₁₆]));
    {
      vectorx := vectorx[i := vectorx[i + 1]];
      i := i + 1;
    }
  }
  if(found != 0) {
    var x: int;
    x := 0;
    while(x < pos)
      decreases pos - x;
      invariant old(x) <= x
        && (forall x₂₁: int ::
              (  old(x) <= x₂₁
                && x₂₁ < x
                 ==> x₂₁ < pos));
    {
      assert vectorx[x] != element;
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

