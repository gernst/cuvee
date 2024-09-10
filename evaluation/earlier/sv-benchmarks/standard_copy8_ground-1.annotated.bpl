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
  var a7: [int]int;
  var a8: [int]int;
  var a9: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant old(a) <= a
      && (forall a₁₂: int ::
            (  old(a) <= a₁₂
              && a₁₂ < a
               ==> (exists nondet_int₁₁₁: int ::
                      -2147483648 <= nondet_int₁₁₁
                      && nondet_int₁₁₁ < 2147483648
                      && a₁₂ < 100000
                      && a1[a₁₂] == nondet_int₁₁₁)))
      && (forall a₁₂: int ::
            (!(  old(a) <= a₁₂
              && a₁₂ < a
            )
               ==> a1[a₁₂] == old(a1)[a₁₂]));
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
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < 100000
                && a2[i₁₆] == a1[i₁₆]))
      && (forall i₁₆: int ::
            (!(  old(i) <= i₁₆
              && i₁₆ < i
            )
               ==> a2[i₁₆] == old(a2)[i₁₆]));
  {
    a2[i] := a1[i];
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
                && a3[i₁₉] == a2[i₁₉]))
      && (forall i₁₉: int ::
            (!(  old(i) <= i₁₉
              && i₁₉ < i
            )
               ==> a3[i₁₉] == old(a3)[i₁₉]));
  {
    a3[i] := a2[i];
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
                && a4[i₂₂] == a3[i₂₂]))
      && (forall i₂₂: int ::
            (!(  old(i) <= i₂₂
              && i₂₂ < i
            )
               ==> a4[i₂₂] == old(a4)[i₂₂]));
  {
    a4[i] := a3[i];
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
                && a5[i₂₅] == a4[i₂₅]))
      && (forall i₂₅: int ::
            (!(  old(i) <= i₂₅
              && i₂₅ < i
            )
               ==> a5[i₂₅] == old(a5)[i₂₅]));
  {
    a5[i] := a4[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₈: int ::
            (  old(i) <= i₂₈
              && i₂₈ < i
               ==> i₂₈ < 100000
                && a6[i₂₈] == a5[i₂₈]))
      && (forall i₂₈: int ::
            (!(  old(i) <= i₂₈
              && i₂₈ < i
            )
               ==> a6[i₂₈] == old(a6)[i₂₈]));
  {
    a6[i] := a5[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₃₁: int ::
            (  old(i) <= i₃₁
              && i₃₁ < i
               ==> i₃₁ < 100000
                && a7[i₃₁] == a6[i₃₁]))
      && (forall i₃₁: int ::
            (!(  old(i) <= i₃₁
              && i₃₁ < i
            )
               ==> a7[i₃₁] == old(a7)[i₃₁]));
  {
    a7[i] := a6[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₃₄: int ::
            (  old(i) <= i₃₄
              && i₃₄ < i
               ==> i₃₄ < 100000
                && a8[i₃₄] == a7[i₃₄]))
      && (forall i₃₄: int ::
            (!(  old(i) <= i₃₄
              && i₃₄ < i
            )
               ==> a8[i₃₄] == old(a8)[i₃₄]));
  {
    a8[i] := a7[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₃₇: int ::
            (  old(i) <= i₃₇
              && i₃₇ < i
               ==> i₃₇ < 100000
                && a9[i₃₇] == a8[i₃₇]))
      && (forall i₃₇: int ::
            (!(  old(i) <= i₃₇
              && i₃₇ < i
            )
               ==> a9[i₃₇] == old(a9)[i₃₇]));
  {
    a9[i] := a8[i];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₄₁: int ::
            (  old(x) <= x₄₁
              && x₄₁ < x
               ==> x₄₁ < 100000));
  {
    assert a1[x] == a9[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

