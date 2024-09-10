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
  var k: int := 0;
  var a: [int]int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall j₄: int, i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> (exists x₃: int ::
                      x₃ == 0
                      && -2147483648 <= x₃
                      && x₃ < 2147483648
                      && i₆ < N
                      && a[i₆] == j₄)))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> a[i₆] == old(a)[i₆]))
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> !((exists x₃: int ::
                      x₃ != 0
                      && -2147483648 <= x₃
                      && x₃ < 2147483648
                      && i₆ < N)
              )));
  {
    var x: int;
    assume -2147483648 <= x && x < 2147483648;
    if(x != 0) {
      break;
    }
    a[i] := j;
    j := j + i;
    k := k - i;
    i := i + 1;
  }
  var l: int := 1;
  while(l < i)
    decreases i - l;
    invariant old(l) <= l
      && (forall l₁₁: int ::
            (  old(l) <= l₁₁
              && l₁₁ < l
               ==> l₁₁ < i));
  {
    assert k <= a[l];
    l := l + 1;
  }
  c#result := 0;
  return;
}

