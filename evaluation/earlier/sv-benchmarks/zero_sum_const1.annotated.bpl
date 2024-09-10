data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var SIZE: int;

var MAX: int;

procedure main()
  returns (c#result: int)
  modifies SIZE, MAX;
{
  SIZE := 0;
  MAX := 100000;
  havoc SIZE;
  assume -2147483648 <= SIZE && SIZE < 2147483648;
  if(1 < SIZE && SIZE < MAX) {
    var i: int;
    var a: [int]int;
    var sum: int := 0;
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₄: int ::
              (  old(i) <= i₄
                && i₄ < i
                 ==> i₄ < SIZE
                  && a[i₄] == 1))
        && (forall i₄: int ::
              (!(  old(i) <= i₄
                && i₄ < i
              )
                 ==> a[i₄] == old(a)[i₄]));
    {
      a[i] := 1;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₈: int ::
              (  old(i) <= i₈
                && i₈ < i
                 ==> i₈ < SIZE));
    {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₁₂: int ::
              (  old(i) <= i₁₂
                && i₁₂ < i
                 ==> i₁₂ < SIZE));
    {
      sum := sum - a[i];
      i := i + 1;
    }
    assert sum == 0;
  }
  c#result := 1;
  return;
}

