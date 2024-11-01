data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  N := 100000;
  var i: int;
  var j: int := 0;
  var a: [int]int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall j₄: int, i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> (exists x₃: int ::
                      x₃ == 0
                      && -2147483648 <= x₃
                      && x₃ < 2147483648
                      && i₅ < N
                      && a[i₅] == j₄)))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]))
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> !((exists x₃: int ::
                      x₃ != 0
                      && -2147483648 <= x₃
                      && x₃ < 2147483648
                      && i₅ < N)
              )));
  {
    var x: int;
    assume -2147483648 <= x && x < 2147483648;
    if(x != 0) {
      break;
    }
    a[i] := j;
    j := j - i;
    i := i + 1;
  }
  var k: int := 4;
  while(k < i)
    decreases i - k;
    invariant old(k) <= k
      && (forall k₉: int ::
            (  old(k) <= k₉
              && k₉ < k
               ==> k₉ < i));
  {
    assert a[k] <= 0;
    k := k + 1;
  }
  c#result := 0;
  return;
}

