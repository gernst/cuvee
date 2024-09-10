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
  var a1: [int]int;
  var a2: [int]int;
  var a3: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant old(a) <= a
      && (forall a₆: int ::
            (  old(a) <= a₆
              && a₆ < a
               ==> (exists nondet_int₁₅: int ::
                      -2147483648 <= nondet_int₁₅
                      && nondet_int₁₅ < 2147483648
                      && a₆ < 100000
                      && a1[a₆] == nondet_int₁₅)))
      && (forall a₆: int ::
            (!(  old(a) <= a₆
              && a₆ < a
            )
               ==> a1[a₆] == old(a1)[a₆]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a1[a] := nondet_int₁;
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < 100000
                && a2[i₁₀] == a1[i₁₀]))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> a2[i₁₀] == old(a2)[i₁₀]));
  {
    a2[i] := a1[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000
                && a3[i₁₃] == a2[i₁₃]))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> a3[i₁₃] == old(a3)[i₁₃]));
  {
    a3[i] := a2[i];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₁₇: int ::
            (  old(x) <= x₁₇
              && x₁₇ < x
               ==> x₁₇ < 100000));
  {
    assert a1[x] == a3[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

