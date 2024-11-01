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
  var a: [int]int;
  var marker: int;
  assume -2147483648 <= marker && marker < 2147483648;
  var pos: int;
  assume -2147483648 <= pos && pos < 2147483648;
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> (exists nondet_int₁₄: int ::
                      -2147483648 <= nondet_int₁₄
                      && nondet_int₁₄ < 2147483648
                      && i₅ < 100000
                      && a[i₅] == nondet_int₁₄)))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[i] := nondet_int₁;
    i := i + 1;
  }
  if(0 <= pos && pos < 100000) {
    a[pos] := marker;
    var i: int := 0;
    while(a[i] != marker)
      invariant old(i) <= i
        && (forall i₈: int ::
              (  old(i) <= i₈
                && i₈ < i
                 ==> a[i₈] != marker));
    {
      i := i + 1;
    }
    assert i <= pos;
  }
  c#result := 0;
  return;
}

