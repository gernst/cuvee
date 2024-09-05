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
  var N: int := 100000;
  var a: [int]int;
  i := 0;
  while(i <= N)
    decreases N + 1 - i;
    invariant true
      && old(i) <= i
      && i <= 1 + N
      && (forall x₄: int ::
            ((exists i₃: int ::
                  if(x₄ == 1 + 2 * i₃) then old(i) <= i₃ && i₃ < i else x₄ == 2 * i₃ && old(i) <= i₃ && i₃ < i)
               ==> (exists i₃: int ::
                      i₃ <= N
                      && if(x₄ == 1 + 2 * i₃) then old(i) <= i₃ && i₃ < i && a[x₄] == 0 else x₄ == 2 * i₃ && old(i) <= i₃ && i₃ < i && a[x₄] == 0)))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                  if(x₄ == 1 + 2 * i₃) then old(i) <= i₃ && i₃ < i else x₄ == 2 * i₃ && old(i) <= i₃ && i₃ < i)
            )
               ==> a[x₄] == old(a[x₄])))
      && (forall i₃: int ::
            (  old(i) <= i₃
              && i₃ < i
               ==> i₃ <= N));
  {
    a := a[2 * i := 0];
    a := a[2 * i + 1 := 0];
    i := i + 1;
  }
  i := 0;
  while(i <= 2 * N)
    decreases 2 * N + 1 - i;
    invariant true
      && old(i) <= i
      && i <= 1 + 2 * N
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ <= 2 * N));
  {
    assert 0 <= a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

