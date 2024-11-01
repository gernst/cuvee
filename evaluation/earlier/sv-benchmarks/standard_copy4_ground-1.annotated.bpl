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
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant old(a) <= a
      && (forall a₈: int ::
            (  old(a) <= a₈
              && a₈ < a
               ==> (exists nondet_int₁₇: int ::
                      -2147483648 <= nondet_int₁₇
                      && nondet_int₁₇ < 2147483648
                      && a₈ < 100000
                      && a1[a₈] == nondet_int₁₇)))
      && (forall a₈: int ::
            (!(  old(a) <= a₈
              && a₈ < a
            )
               ==> a1[a₈] == old(a1)[a₈]));
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
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < 100000
                && a2[i₁₂] == a1[i₁₂]))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> a2[i₁₂] == old(a2)[i₁₂]));
  {
    a2[i] := a1[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₅: int ::
            (  old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < 100000
                && a3[i₁₅] == a2[i₁₅]))
      && (forall i₁₅: int ::
            (!(  old(i) <= i₁₅
              && i₁₅ < i
            )
               ==> a3[i₁₅] == old(a3)[i₁₅]));
  {
    a3[i] := a2[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 100000
                && a4[i₁₈] == a3[i₁₈]))
      && (forall i₁₈: int ::
            (!(  old(i) <= i₁₈
              && i₁₈ < i
            )
               ==> a4[i₁₈] == old(a4)[i₁₈]));
  {
    a4[i] := a3[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₁: int ::
            (  old(i) <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < 100000
                && a5[i₂₁] == a4[i₂₁]))
      && (forall i₂₁: int ::
            (!(  old(i) <= i₂₁
              && i₂₁ < i
            )
               ==> a5[i₂₁] == old(a5)[i₂₁]));
  {
    a5[i] := a4[i];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₂₅: int ::
            (  old(x) <= x₂₅
              && x₂₅ < x
               ==> x₂₅ < 100000));
  {
    assert a1[x] == a5[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

