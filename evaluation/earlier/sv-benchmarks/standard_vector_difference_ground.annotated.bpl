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
  var c: [int]int;
  var i: int := 0;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> (exists nondet_int₁₄: int, nondet_int₂₅: int ::
                      -2147483648 <= nondet_int₂₅
                      && nondet_int₂₅ < 2147483648
                      && -2147483648 <= nondet_int₁₄
                      && nondet_int₁₄ < 2147483648
                      && i₆ < 100000
                      && a[i₆] == nondet_int₁₄
                      && b[i₆] == nondet_int₂₅)))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> a[i₆] == old(a)[i₆]
                && b[i₆] == old(b)[i₆]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[i] := nondet_int₁;
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    b[i] := nondet_int₂;
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < 100000
                && c[i₁₀] == -b[i₁₀] + a[i₁₀]))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> c[i₁₀] == old(c)[i₁₀]));
  {
    c[i] := a[i] - b[i];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₁₄: int ::
            (  old(x) <= x₁₄
              && x₁₄ < x
               ==> x₁₄ < 100000));
  {
    assert c[x] == a[x] - b[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

