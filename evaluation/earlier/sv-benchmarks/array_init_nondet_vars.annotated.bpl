data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var j: int;
  assume -2147483648 <= j && j < 2147483648;
  var n: int;
  assume -2147483648 <= n && n < 2147483648;
  assume n < 100000;
  var a: [int]int;
  assume 0 < j && j < 10000;
  i := 1;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> (exists k₅: int ::
                      0 < k₅
                      && k₅ < 10000
                      && -2147483648 <= k₅
                      && k₅ < 2147483648
                      && i₆ < n
                      && a[i₆] == j + k₅ + i₆)))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> a[i₆] == old(a)[i₆]));
  {
    var k: int;
    assume -2147483648 <= k && k < 2147483648;
    assume 0 < k && k < 10000;
    a[i] := i + j + k;
    i := i + 1;
  }
  i := 1;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < n));
  {
    assert i + 2 <= a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

