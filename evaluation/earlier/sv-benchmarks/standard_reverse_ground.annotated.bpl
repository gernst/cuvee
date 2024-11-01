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
  var b: [int]int;
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> (exists nondet_int₁₄: int ::
                      -2147483648 <= nondet_int₁₄
                      && nondet_int₁₄ < 2147483648
                      && i₅ < 100000
                      && a[i₅] == nondet_int₁₄)))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[i] := nondet_int₁;
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ < 100000
                && b[i₈] == a[99999 + -i₈]))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> b[i₈] == old(b)[i₈]));
  {
    b[i] := a[100000 - i - 1];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₁₂: int ::
            (  old(x) <= x₁₂
              && x₁₂ < x
               ==> x₁₂ < 100000));
  {
    assert a[x] == b[100000 - x - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}

