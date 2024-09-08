data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

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
  var a0: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant old(a) <= a
      && a <= 100000
      && (forall a₁₃: int ::
            (  old(a) <= a₁₃
              && a₁₃ < a
               ==> (exists __VERIFIER_nondet_int₁₁₂: int ::
                      a₁₃ < 100000
                      && a1[a₁₃] == __VERIFIER_nondet_int₁₁₂)))
      && (forall a₁₃: int ::
            (!(  old(a) <= a₁₃
              && a₁₃ < a
            )
               ==> a1[a₁₃] == old(a1)[a₁₃]));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 100000
                && a2[i₁₇] == a1[i₁₇]))
      && (forall i₁₇: int ::
            (!(  old(i) <= i₁₇
              && i₁₇ < i
            )
               ==> a2[i₁₇] == old(a2)[i₁₇]));
  {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₂₀: int ::
            (  old(i) <= i₂₀
              && i₂₀ < i
               ==> i₂₀ < 100000
                && a3[i₂₀] == a2[i₂₀]))
      && (forall i₂₀: int ::
            (!(  old(i) <= i₂₀
              && i₂₀ < i
            )
               ==> a3[i₂₀] == old(a3)[i₂₀]));
  {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₂₃: int ::
            (  old(i) <= i₂₃
              && i₂₃ < i
               ==> i₂₃ < 100000
                && a4[i₂₃] == a3[i₂₃]))
      && (forall i₂₃: int ::
            (!(  old(i) <= i₂₃
              && i₂₃ < i
            )
               ==> a4[i₂₃] == old(a4)[i₂₃]));
  {
    a4 := a4[i := a3[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₂₆: int ::
            (  old(i) <= i₂₆
              && i₂₆ < i
               ==> i₂₆ < 100000
                && a5[i₂₆] == a4[i₂₆]))
      && (forall i₂₆: int ::
            (!(  old(i) <= i₂₆
              && i₂₆ < i
            )
               ==> a5[i₂₆] == old(a5)[i₂₆]));
  {
    a5 := a5[i := a4[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₂₉: int ::
            (  old(i) <= i₂₉
              && i₂₉ < i
               ==> i₂₉ < 100000
                && a6[i₂₉] == a5[i₂₉]))
      && (forall i₂₉: int ::
            (!(  old(i) <= i₂₉
              && i₂₉ < i
            )
               ==> a6[i₂₉] == old(a6)[i₂₉]));
  {
    a6 := a6[i := a5[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₃₂: int ::
            (  old(i) <= i₃₂
              && i₃₂ < i
               ==> i₃₂ < 100000
                && a7[i₃₂] == a6[i₃₂]))
      && (forall i₃₂: int ::
            (!(  old(i) <= i₃₂
              && i₃₂ < i
            )
               ==> a7[i₃₂] == old(a7)[i₃₂]));
  {
    a7 := a7[i := a6[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₃₅: int ::
            (  old(i) <= i₃₅
              && i₃₅ < i
               ==> i₃₅ < 100000
                && a8[i₃₅] == a7[i₃₅]))
      && (forall i₃₅: int ::
            (!(  old(i) <= i₃₅
              && i₃₅ < i
            )
               ==> a8[i₃₅] == old(a8)[i₃₅]));
  {
    a8 := a8[i := a7[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₃₈: int ::
            (  old(i) <= i₃₈
              && i₃₈ < i
               ==> i₃₈ < 100000
                && a9[i₃₈] == a8[i₃₈]))
      && (forall i₃₈: int ::
            (!(  old(i) <= i₃₈
              && i₃₈ < i
            )
               ==> a9[i₃₈] == old(a9)[i₃₈]));
  {
    a9 := a9[i := a8[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₄₁: int ::
            (  old(i) <= i₄₁
              && i₄₁ < i
               ==> i₄₁ < 100000
                && a0[i₄₁] == a9[i₄₁]))
      && (forall i₄₁: int ::
            (!(  old(i) <= i₄₁
              && i₄₁ < i
            )
               ==> a0[i₄₁] == old(a0)[i₄₁]));
  {
    a0 := a0[i := a9[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && x <= 100000
      && (forall x₄₅: int ::
            (  old(x) <= x₄₅
              && x₄₅ < x
               ==> x₄₅ < 100000));
  {
    assert a1[x] == a0[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

