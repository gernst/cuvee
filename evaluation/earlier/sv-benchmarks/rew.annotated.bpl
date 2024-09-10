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
    var val2: int := 3;
    var val1: int := 0;
    var low: int := 2;
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₄: int ::
              (  old(i) <= i₄
                && i₄ < i
                 ==> 1 + i₄ < SIZE
                    && i₄ < SIZE
                    && a[i₄] == val2
                    && (1 + i₄ != i₄
                       ==> a[1 + i₄] == val1)
                  ||   !(1 + i₄ < SIZE
                    )
                    && i₄ < SIZE
                    && a[i₄] == val2))
        && (forall i₄: int ::
              (!(  old(i) <= i₄
                && i₄ < i
              )
                 ==> a[i₄] == old(a)[i₄]
                  && a[1 + i₄] == old(a)[1 + i₄]));
    {
      if(i + 1 < SIZE) {
        a[(i + 1)] := val1;
      }
      a[i] := val2;
      i := i + 1;
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
      assert low <= a[i];
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

