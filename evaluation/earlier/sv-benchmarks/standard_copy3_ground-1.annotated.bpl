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
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant old(a) <= a
      && a <= 100000
      && (forall a₇: int ::
            (  old(a) <= a₇
              && a₇ < a
               ==> (exists __VERIFIER_nondet_int₁₆: int ::
                      a₇ < 100000
                      && a1[a₇] == __VERIFIER_nondet_int₁₆)))
      && (forall a₇: int ::
            (!(  old(a) <= a₇
              && a₇ < a
            )
               ==> a1[a₇] == old(a1)[a₇]));
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
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 100000
                && a2[i₁₁] == a1[i₁₁]))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> a2[i₁₁] == old(a2)[i₁₁]));
  {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 100000
                && a3[i₁₄] == a2[i₁₄]))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> a3[i₁₄] == old(a3)[i₁₄]));
  {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 100000
                && a4[i₁₇] == a3[i₁₇]))
      && (forall i₁₇: int ::
            (!(  old(i) <= i₁₇
              && i₁₇ < i
            )
               ==> a4[i₁₇] == old(a4)[i₁₇]));
  {
    a4 := a4[i := a3[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && x <= 100000
      && (forall x₂₁: int ::
            (  old(x) <= x₂₁
              && x₂₁ < x
               ==> x₂₁ < 100000));
  {
    assert a1[x] == a4[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

