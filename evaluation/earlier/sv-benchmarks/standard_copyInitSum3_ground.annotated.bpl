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
  var b: [int]int;
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₃: int ::
            (  old(i) <= i₃
              && i₃ < i
               ==> i₃ < 100000
                && a[i₃] == 42))
      && (forall i₃: int ::
            (!(  old(i) <= i₃
              && i₃ < i
            )
               ==> a[i₃] == old(a)[i₃]));
  {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> i₆ < 100000
                && b[i₆] == a[i₆]))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> b[i₆] == old(b)[i₆]));
  {
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < 100000
                && b[i₉] == i₉ + old(b)[i₉]))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> b[i₉] == old(b)[i₉]));
  {
    b := b[i := b[i] + i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < 100000
                && b[i₁₂] == -a[i₁₂] + old(b)[i₁₂]))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> b[i₁₂] == old(b)[i₁₂]));
  {
    b := b[i := b[i] - a[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && x <= 100000
      && (forall x₁₆: int ::
            (  old(x) <= x₁₆
              && x₁₆ < x
               ==> x₁₆ < 100000));
  {
    assert b[x] == x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

