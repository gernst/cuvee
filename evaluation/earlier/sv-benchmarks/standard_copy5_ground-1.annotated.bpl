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
  var a4: [int]int;
  var a5: [int]int;
  var a6: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant old(a) <= a
      && (forall a₉: int ::
            (  old(a) <= a₉
              && a₉ < a
               ==> (exists nondet_int₁₈: int ::
                      -2147483648 <= nondet_int₁₈
                      && nondet_int₁₈ < 2147483648
                      && a₉ < 100000
                      && a1[a₉] == nondet_int₁₈)))
      && (forall a₉: int ::
            (!(  old(a) <= a₉
              && a₉ < a
            )
               ==> a1[a₉] == old(a1)[a₉]));
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
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000
                && a2[i₁₃] == a1[i₁₃]))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> a2[i₁₃] == old(a2)[i₁₃]));
  {
    a2[i] := a1[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < 100000
                && a3[i₁₆] == a2[i₁₆]))
      && (forall i₁₆: int ::
            (!(  old(i) <= i₁₆
              && i₁₆ < i
            )
               ==> a3[i₁₆] == old(a3)[i₁₆]));
  {
    a3[i] := a2[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₉: int ::
            (  old(i) <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < 100000
                && a4[i₁₉] == a3[i₁₉]))
      && (forall i₁₉: int ::
            (!(  old(i) <= i₁₉
              && i₁₉ < i
            )
               ==> a4[i₁₉] == old(a4)[i₁₉]));
  {
    a4[i] := a3[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₂: int ::
            (  old(i) <= i₂₂
              && i₂₂ < i
               ==> i₂₂ < 100000
                && a5[i₂₂] == a4[i₂₂]))
      && (forall i₂₂: int ::
            (!(  old(i) <= i₂₂
              && i₂₂ < i
            )
               ==> a5[i₂₂] == old(a5)[i₂₂]));
  {
    a5[i] := a4[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₅: int ::
            (  old(i) <= i₂₅
              && i₂₅ < i
               ==> i₂₅ < 100000
                && a6[i₂₅] == a5[i₂₅]))
      && (forall i₂₅: int ::
            (!(  old(i) <= i₂₅
              && i₂₅ < i
            )
               ==> a6[i₂₅] == old(a6)[i₂₅]));
  {
    a6[i] := a5[i];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₂₉: int ::
            (  old(x) <= x₂₉
              && x₂₉ < x
               ==> x₂₉ < 100000));
  {
    assert a1[x] == a6[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

