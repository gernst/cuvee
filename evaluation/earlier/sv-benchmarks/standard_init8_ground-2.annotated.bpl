data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> i₂ < 100000
                && a[i₂] == 42))
      && (forall i₂: int ::
            (!(  old(i) <= i₂
              && i₂ < i
            )
               ==> a[i₂] == old(a)[i₂]));
  {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < 100000
                && a[i₅] == 43))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]));
  {
    a := a[i := 43];
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
                && a[i₈] == 44))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> a[i₈] == old(a)[i₈]));
  {
    a := a[i := 44];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 100000
                && a[i₁₁] == 45))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> a[i₁₁] == old(a)[i₁₁]));
  {
    a := a[i := 45];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 100000
                && a[i₁₄] == 46))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> a[i₁₄] == old(a)[i₁₄]));
  {
    a := a[i := 46];
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
                && a[i₁₇] == 47))
      && (forall i₁₇: int ::
            (!(  old(i) <= i₁₇
              && i₁₇ < i
            )
               ==> a[i₁₇] == old(a)[i₁₇]));
  {
    a := a[i := 47];
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
                && a[i₂₀] == 48))
      && (forall i₂₀: int ::
            (!(  old(i) <= i₂₀
              && i₂₀ < i
            )
               ==> a[i₂₀] == old(a)[i₂₀]));
  {
    a := a[i := 48];
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
                && a[i₂₃] == 49))
      && (forall i₂₃: int ::
            (!(  old(i) <= i₂₃
              && i₂₃ < i
            )
               ==> a[i₂₃] == old(a)[i₂₃]));
  {
    a := a[i := 49];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₂₇: int ::
            (  old(x) <= x₂₇
              && x₂₇ < x
               ==> x₂₇ < 100000));
  {
    assert a[x] == 49;
    x := x + 1;
  }
  c#result := 0;
  return;
}

