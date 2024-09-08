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
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant old(a) <= a
      && a <= 100000
      && (forall a₁₁: int ::
            (  old(a) <= a₁₁
              && a₁₁ < a
               ==> (exists __VERIFIER_nondet_int₁₁₀: int ::
                      a₁₁ < 100000
                      && a1[a₁₁] == __VERIFIER_nondet_int₁₁₀)))
      && (forall a₁₁: int ::
            (!(  old(a) <= a₁₁
              && a₁₁ < a
            )
               ==> a1[a₁₁] == old(a1)[a₁₁]));
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
      && (forall i₁₅: int ::
            (  old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < 100000
                && a2[i₁₅] == a1[i₁₅]))
      && (forall i₁₅: int ::
            (!(  old(i) <= i₁₅
              && i₁₅ < i
            )
               ==> a2[i₁₅] == old(a2)[i₁₅]));
  {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 100000
                && a3[i₁₈] == a2[i₁₈]))
      && (forall i₁₈: int ::
            (!(  old(i) <= i₁₈
              && i₁₈ < i
            )
               ==> a3[i₁₈] == old(a3)[i₁₈]));
  {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₂₁: int ::
            (  old(i) <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < 100000
                && a4[i₂₁] == a3[i₂₁]))
      && (forall i₂₁: int ::
            (!(  old(i) <= i₂₁
              && i₂₁ < i
            )
               ==> a4[i₂₁] == old(a4)[i₂₁]));
  {
    a4 := a4[i := a3[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₂₄: int ::
            (  old(i) <= i₂₄
              && i₂₄ < i
               ==> i₂₄ < 100000
                && a5[i₂₄] == a4[i₂₄]))
      && (forall i₂₄: int ::
            (!(  old(i) <= i₂₄
              && i₂₄ < i
            )
               ==> a5[i₂₄] == old(a5)[i₂₄]));
  {
    a5 := a5[i := a4[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₂₇: int ::
            (  old(i) <= i₂₇
              && i₂₇ < i
               ==> i₂₇ < 100000
                && a6[i₂₇] == a5[i₂₇]))
      && (forall i₂₇: int ::
            (!(  old(i) <= i₂₇
              && i₂₇ < i
            )
               ==> a6[i₂₇] == old(a6)[i₂₇]));
  {
    a6 := a6[i := a5[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₃₀: int ::
            (  old(i) <= i₃₀
              && i₃₀ < i
               ==> i₃₀ < 100000
                && a7[i₃₀] == a6[i₃₀]))
      && (forall i₃₀: int ::
            (!(  old(i) <= i₃₀
              && i₃₀ < i
            )
               ==> a7[i₃₀] == old(a7)[i₃₀]));
  {
    a7 := a7[i := a6[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₃₃: int ::
            (  old(i) <= i₃₃
              && i₃₃ < i
               ==> i₃₃ < 100000
                && a8[i₃₃] == a7[i₃₃]))
      && (forall i₃₃: int ::
            (!(  old(i) <= i₃₃
              && i₃₃ < i
            )
               ==> a8[i₃₃] == old(a8)[i₃₃]));
  {
    a8 := a8[i := a7[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && x <= 100000
      && (forall x₃₇: int ::
            (  old(x) <= x₃₇
              && x₃₇ < x
               ==> x₃₇ < 100000));
  {
    assert a1[x] == a8[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

