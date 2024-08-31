data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var a: [int]int;

procedure main()
  returns (c#result: int)
  modifies a;
{
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₃: int ::
            ((exists i₂: int ::
                    x₃ == i₂
                    && old(i) <= i₂
                    && i₂ < i)
               ==> (exists i₂: int ::
                        0 <= i₂
                        && i₂ <= 10000
                        && i₂ < 100000
                        && x₃ == i₂
                        && old(i) <= i₂
                        && i₂ < i
                        && a[x₃] == 10)
                || (exists i₂: int ::
                        !(  0 <= i₂
                          && i₂ <= 10000
                        )
                        && i₂ < 100000
                        && x₃ == i₂
                        && old(i) <= i₂
                        && i₂ < i
                        && a[x₃] == 0)))
      && (forall x₃: int ::
            (!((exists i₂: int ::
                    x₃ == i₂
                    && old(i) <= i₂
                    && i₂ < i)
            )
               ==> a[x₃] == old(a[x₃])))
      && (forall i₂: int ::
            (  old(i₂) <= i₂
              && old(i) <= i₂
              && i₂ < i
               ==> i₂ < 100000));
  {
    if(0 <= i && i <= 10000) {
      a := a[i := 10];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall i₆: int ::
            (  old(i₆) <= i₆
              && old(i) <= i₆
              && i₆ < i
               ==> i₆ < 100000));
  {
    assert a[i] == 10;
    i := i + 1;
  }
  c#result := 0;
  return;
}

