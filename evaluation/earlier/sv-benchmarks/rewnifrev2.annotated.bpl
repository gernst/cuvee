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
  var i: int;
  if(1 < SIZE && SIZE < MAX) {
    var a: [int]int;
    i := SIZE - 2;
    while(0 <= i)
      decreases i + 1 - 0;
      invariant i <= old(i)
        && (forall i₄: int ::
              (  i < i₄
                && i₄ <= old(i)
                 ==> 0 <= i₄
                  && a[1 + i₄] == 1 + i₄
                  && (i₄ != 1 + i₄
                     ==> a[i₄] == i₄)))
        && (forall i₄: int ::
              (!(  i < i₄
                && i₄ <= old(i)
              )
                 ==> a[1 + i₄] == old(a)[1 + i₄]
                  && a[i₄] == old(a)[i₄]));
    {
      a[i] := i;
      a[(i + 1)] := i + 1;
      i := i - 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₇: int ::
              (  old(i) <= i₇
                && i₇ < i
                 ==> i₇ < SIZE));
    {
      assert i <= a[i];
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

