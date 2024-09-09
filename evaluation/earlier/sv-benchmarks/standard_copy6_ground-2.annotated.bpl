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
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant old(a) <= a
      && (forall a₁₀: int ::
            (  old(a) <= a₁₀
              && a₁₀ < a
               ==> (exists __VERIFIER_nondet_int₁₉: int ::
                      a₁₀ < 100000
                      && a1[a₁₀] == __VERIFIER_nondet_int₁₉)))
      && (forall a₁₀: int ::
            (!(  old(a) <= a₁₀
              && a₁₀ < a
            )
               ==> a1[a₁₀] == old(a1)[a₁₀]));
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
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 100000
                && a2[i₁₄] == a1[i₁₄]))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> a2[i₁₄] == old(a2)[i₁₄]));
  {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 100000
                && a3[i₁₇] == a2[i₁₇]))
      && (forall i₁₇: int ::
            (!(  old(i) <= i₁₇
              && i₁₇ < i
            )
               ==> a3[i₁₇] == old(a3)[i₁₇]));
  {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₀: int ::
            (  old(i) <= i₂₀
              && i₂₀ < i
               ==> i₂₀ < 100000
                && a4[i₂₀] == a3[i₂₀]))
      && (forall i₂₀: int ::
            (!(  old(i) <= i₂₀
              && i₂₀ < i
            )
               ==> a4[i₂₀] == old(a4)[i₂₀]));
  {
    a4 := a4[i := a3[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₃: int ::
            (  old(i) <= i₂₃
              && i₂₃ < i
               ==> i₂₃ < 100000
                && a5[i₂₃] == a4[i₂₃]))
      && (forall i₂₃: int ::
            (!(  old(i) <= i₂₃
              && i₂₃ < i
            )
               ==> a5[i₂₃] == old(a5)[i₂₃]));
  {
    a5 := a5[i := a4[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₆: int ::
            (  old(i) <= i₂₆
              && i₂₆ < i
               ==> i₂₆ < 100000
                && a6[i₂₆] == a5[i₂₆]))
      && (forall i₂₆: int ::
            (!(  old(i) <= i₂₆
              && i₂₆ < i
            )
               ==> a6[i₂₆] == old(a6)[i₂₆]));
  {
    a6 := a6[i := a5[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₉: int ::
            (  old(i) <= i₂₉
              && i₂₉ < i
               ==> i₂₉ < 100000
                && a7[i₂₉] == a6[i₂₉]))
      && (forall i₂₉: int ::
            (!(  old(i) <= i₂₉
              && i₂₉ < i
            )
               ==> a7[i₂₉] == old(a7)[i₂₉]));
  {
    a7 := a7[i := a6[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₃₃: int ::
            (  old(x) <= x₃₃
              && x₃₃ < x
               ==> x₃₃ < 100000));
  {
    assert a1[x] == a7[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

