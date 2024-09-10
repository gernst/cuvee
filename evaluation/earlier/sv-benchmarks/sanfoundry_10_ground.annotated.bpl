data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var n: int := 100000;
  var pos: int;
  var element: int;
  assume -2147483648 <= element && element < 2147483648;
  var found: int := 0;
  var vectorx: [int]int;
  i := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> (exists nondet_int₁₅: int ::
                      -2147483648 <= nondet_int₁₅
                      && nondet_int₁₅ < 2147483648
                      && i₆ < n
                      && vectorx[i₆] == nondet_int₁₅)))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> vectorx[i₆] == old(vectorx)[i₆]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    vectorx[i] := nondet_int₁;
    i := i + 1;
  }
  i := 0;
  while(i < n && !(found != 0))
    decreases n - i;
    invariant old(i) <= i
      && (forall found₉: int, i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> vectorx[i₁₁] == element
                  && i₁₁ < n
                  && found₉ == 0
                ||   vectorx[i₁₁] != element
                  && i₁₁ < n
                  && found₉ == 0));
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
        && (forall i₁₅: int ::
              (  old(i) <= i₁₅
                && i₁₅ < i
                 ==> i₁₅ < -1 + n
                  && vectorx[i₁₅] == old(vectorx)[1 + i₁₅]))
        && (forall i₁₅: int ::
              (!(  old(i) <= i₁₅
                && i₁₅ < i
              )
                 ==> vectorx[i₁₅] == old(vectorx)[i₁₅]));
    {
      vectorx[i] := vectorx[i + 1];
      i := i + 1;
    }
  }
  if(found != 0) {
    var x: int;
    x := 0;
    while(x < pos)
      decreases pos - x;
      invariant old(x) <= x
        && (forall x₂₀: int ::
              (  old(x) <= x₂₀
                && x₂₀ < x
                 ==> x₂₀ < pos));
    {
      assert vectorx[x] != element;
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

