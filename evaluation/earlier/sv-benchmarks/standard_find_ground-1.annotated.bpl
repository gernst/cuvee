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
  var a: [int]int;
  var e: int;
  assume -2147483648 <= e && e < 2147483648;
  var i: int := 0;
  var j: int;
  j := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant old(j) <= j
      && (forall j₅: int ::
            (  old(j) <= j₅
              && j₅ < j
               ==> (exists nondet_int₁₄: int ::
                      -2147483648 <= nondet_int₁₄
                      && nondet_int₁₄ < 2147483648
                      && j₅ < 100000
                      && a[j₅] == nondet_int₁₄)))
      && (forall j₅: int ::
            (!(  old(j) <= j₅
              && j₅ < j
            )
               ==> a[j₅] == old(a)[j₅]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[j] := nondet_int₁;
    j := j + 1;
  }
  while(i < 100000 && a[i] != e)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ < 100000
                && a[i₈] != e));
  {
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i)
    decreases i - x;
    invariant old(x) <= x
      && (forall x₁₁: int ::
            (  old(x) <= x₁₁
              && x₁₁ < x
               ==> x₁₁ < i));
  {
    assert a[x] != e;
    x := x + 1;
  }
  c#result := 0;
  return;
}

