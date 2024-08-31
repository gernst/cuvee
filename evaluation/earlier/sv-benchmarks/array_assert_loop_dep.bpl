data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var a: [int]int;
  i := 0;
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
                      && a[x₄] == 10)))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
            )
               ==> a[x₄] == old(a[x₄])))
      && (forall i₃: int ::
            (  old(i₃) <= i₃
              && old(i) <= i₃
              && i₃ < i
               ==> i₃ < 100000));
  {
    a := a[i := 10];
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
                    x₈ == 1 + i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists i₇: int ::
                      1 + i₇ != 15000
                      && i₇ < 100000
                      && x₈ == 1 + i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && a[x₈] == 20)))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == 1 + i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> a[x₈] == old(a[x₈])))
      && (forall i₇: int ::
            (  old(i₇) <= i₇
              && old(i) <= i₇
              && i₇ < i
               ==> i₇ < 100000));
  {
    assert a[i] == 10;
    if(i + 1 != 15000) {
      a := a[i + 1 := 20];
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

