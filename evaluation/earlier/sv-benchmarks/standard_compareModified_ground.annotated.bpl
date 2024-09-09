data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

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
               ==> (exists __VERIFIER_nondet_int₁₄: int, __VERIFIER_nondet_int₂₅: int ::
                      j₆ < 100000
                      && a[j₆] == __VERIFIER_nondet_int₁₄
                      && b[j₆] == __VERIFIER_nondet_int₂₅)))
      && (forall j₆: int ::
            (!(  old(j) <= j₆
              && j₆ < j
            )
               ==> a[j₆] == old(a)[j₆]
                && b[j₆] == old(b)[j₆]));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[j := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    b := b[j := __VERIFIER_nondet_int₂];
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
    c := c[i := a[i]];
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

