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
      && old(i) <= i
      && i <= 100000
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
               ==> (exists i₃: int ::
                      i₃ < 100000
                      && x₄ == i₃
                      && old(i) <= i₃
                      && i₃ < i
                      && a[x₄] == 42)))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
            )
               ==> a[x₄] == old(a[x₄])))
      && (forall i₃: int ::
            (  old(i) <= i₃
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
      && old(i) <= i
      && i <= 100000
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists i₇: int ::
                      i₇ < 100000
                      && x₈ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && b[x₈] == a[i₇])))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> b[x₈] == old(b[x₈])))
      && (forall i₇: int ::
            (  old(i) <= i₇
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
      && old(i) <= i
      && i <= 100000
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
               ==> (exists i₁₁: int ::
                      i₁₁ < 100000
                      && x₁₂ == i₁₁
                      && old(i) <= i₁₁
                      && i₁₁ < i
                      && b[x₁₂] == old(b)[i₁₁] + i₁₁)))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
            )
               ==> b[x₁₂] == old(b[x₁₂])))
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 100000));
  {
    b := b[i := b[i] + i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₆: int ::
            ((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
               ==> (exists i₁₅: int ::
                      i₁₅ < 100000
                      && x₁₆ == i₁₅
                      && old(i) <= i₁₅
                      && i₁₅ < i
                      && b[x₁₆] == -a[i₁₅] + old(b)[i₁₅])))
      && (forall x₁₆: int ::
            (!((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
            )
               ==> b[x₁₆] == old(b[x₁₆])))
      && (forall i₁₅: int ::
            (  old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < 100000));
  {
    b := b[i := b[i] - a[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₂₀: int ::
            (  old(x) <= x₂₀
              && x₂₀ < x
               ==> x₂₀ < 100000));
  {
    assert b[x] == x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

