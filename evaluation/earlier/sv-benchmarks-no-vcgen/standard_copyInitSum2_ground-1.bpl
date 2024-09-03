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
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && 0 <= i₃
                    && i₃ < i)
               ==> (exists i₃: int ::
                      i₃ < 100000
                      && x₄ == i₃
                      && 0 <= i₃
                      && i₃ < i
                      && a[x₄] == 42)))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && 0 <= i₃
                    && i₃ < i)
            )
               ==> a[x₄] == old(a[x₄])))
      && (forall i₃: int ::
            (  0 <= i₃
              && i₃ < i
               ==> i₃ < 100000));
  {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && 0 <= i₇
                    && i₇ < i)
               ==> (exists i₇: int ::
                      i₇ < 100000
                      && x₈ == i₇
                      && 0 <= i₇
                      && i₇ < i
                      && b[x₈] == a[i₇])))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && 0 <= i₇
                    && i₇ < i)
            )
               ==> b[x₈] == old(b[x₈])))
      && (forall i₇: int ::
            (  0 <= i₇
              && i₇ < i
               ==> i₇ < 100000));
  {
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && 0 <= i₁₁
                    && i₁₁ < i)
               ==> (exists i₁₁: int ::
                      i₁₁ < 100000
                      && x₁₂ == i₁₁
                      && 0 <= i₁₁
                      && i₁₁ < i
                      && a[x₁₂] == i₁₁ + b[i₁₁])))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && 0 <= i₁₁
                    && i₁₁ < i)
            )
               ==> a[x₁₂] == old(a[x₁₂])))
      && (forall i₁₁: int ::
            (  0 <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 100000));
  {
    a := a[i := b[i] + i];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₁₆: int ::
            (  0 <= x₁₆
              && x₁₆ < x
               ==> x₁₆ < 100000));
  {
    assert b[x] == 42 + x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

