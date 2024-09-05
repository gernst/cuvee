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
    invariant true
      && old(i) <= i
      && i <= n
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                      i₇ < n
                      && x₈ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && vectorx[x₈] == __VERIFIER_nondet_int₂₆)))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> vectorx[x₈] == old(vectorx[x₈])))
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < n));
  {
    var __VERIFIER_nondet_int₂: int;
    vectorx := vectorx[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < n && !(found != 0))
    decreases n - i;
    invariant true
      && old(i) <= i
      && i <= n
      && (forall found₁₁: int, i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < n
                && found₁₁ == 0));
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
      invariant true
        && old(i) <= i
        && i <= -1 + n
        && (forall x₁₈: int ::
              ((exists i₁₇: int ::
                      x₁₈ == i₁₇
                      && old(i) <= i₁₇
                      && i₁₇ < i)
                 ==> (exists i₁₇: int ::
                        i₁₇ < -1 + n
                        && x₁₈ == i₁₇
                        && old(i) <= i₁₇
                        && i₁₇ < i
                        && vectorx[x₁₈] == old(vectorx)[1 + i₁₇])))
        && (forall x₁₈: int ::
              (!((exists i₁₇: int ::
                      x₁₈ == i₁₇
                      && old(i) <= i₁₇
                      && i₁₇ < i)
              )
                 ==> vectorx[x₁₈] == old(vectorx[x₁₈])))
        && (forall i₁₇: int ::
              (  old(i) <= i₁₇
                && i₁₇ < i
                 ==> i₁₇ < -1 + n));
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
      invariant true
        && old(x) <= x
        && x <= pos
        && (forall x₂₃: int ::
              (  old(x) <= x₂₃
                && x₂₃ < x
                 ==> x₂₃ < pos));
    {
      assert vectorx[x] != element;
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

