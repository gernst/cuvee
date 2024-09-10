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
  var b: [int]int;
  var i: int := 0;
  var c: [int]int;
  var rv: int := 1;
  var j: int := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant old(j) <= j
      && (forall j₆: int ::
            (  old(j) <= j₆
              && j₆ < j
               ==> (exists nondet_int₁₄: int, nondet_int₂₅: int ::
                      -2147483648 <= nondet_int₂₅
                      && nondet_int₂₅ < 2147483648
                      && -2147483648 <= nondet_int₁₄
                      && nondet_int₁₄ < 2147483648
                      && j₆ < 100000
                      && a[j₆] == nondet_int₁₄
                      && b[j₆] == nondet_int₂₅)))
      && (forall j₆: int ::
            (!(  old(j) <= j₆
              && j₆ < j
            )
               ==> a[j₆] == old(a)[j₆]
                && b[j₆] == old(b)[j₆]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[j] := nondet_int₁;
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    b[j] := nondet_int₂;
    j := j + 1;
  }
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> a[i₁₁] != b[i₁₁]
                  && i₁₁ < 100000
                  && c[i₁₁] == a[i₁₁]
                ||   a[i₁₁] == b[i₁₁]
                  && i₁₁ < 100000
                  && c[i₁₁] == a[i₁₁]))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> c[i₁₁] == old(c)[i₁₁]));
  {
    if(a[i] != b[i]) {
      rv := 0;
    }
    c[i] := a[i];
    i := i + 1;
  }
  var x: int;
  if(rv != 0) {
    x := 0;
    while(x < 100000)
      decreases 100000 - x;
      invariant old(x) <= x
        && (forall x₁₆: int ::
              (  old(x) <= x₁₆
                && x₁₆ < x
                 ==> x₁₆ < 100000));
    {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₁₈: int ::
            (  old(x) <= x₁₈
              && x₁₈ < x
               ==> x₁₈ < 100000));
  {
    assert a[x] == c[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

