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
    invariant true
      && old(j) <= j
      && j <= 100000
      && (forall x₇: int ::
            ((exists j₆: int ::
                    x₇ == j₆
                    && old(j) <= j₆
                    && j₆ < j)
               ==> (exists __VERIFIER_nondet_int₁₄: int, j₆: int ::
                      j₆ < 100000
                      && x₇ == j₆
                      && old(j) <= j₆
                      && j₆ < j
                      && a[x₇] == __VERIFIER_nondet_int₁₄)))
      && (forall x₇: int ::
            (!((exists j₆: int ::
                    x₇ == j₆
                    && old(j) <= j₆
                    && j₆ < j)
            )
               ==> a[x₇] == old(a[x₇])))
      && (forall x₈: int ::
            ((exists j₆: int ::
                    x₈ == j₆
                    && old(j) <= j₆
                    && j₆ < j)
               ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                      j₆ < 100000
                      && x₈ == j₆
                      && old(j) <= j₆
                      && j₆ < j
                      && b[x₈] == __VERIFIER_nondet_int₂₅)))
      && (forall x₈: int ::
            (!((exists j₆: int ::
                    x₈ == j₆
                    && old(j) <= j₆
                    && j₆ < j)
            )
               ==> b[x₈] == old(b[x₈])))
      && (forall j₆: int ::
            (  old(j) <= j₆
              && j₆ < j
               ==> j₆ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[j := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    b := b[j := __VERIFIER_nondet_int₂];
    j := j + 1;
  }
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
               ==> (exists i₁₃: int ::
                        a[i₁₃] != b[i₁₃]
                        && i₁₃ < 100000
                        && x₁₄ == i₁₃
                        && old(i) <= i₁₃
                        && i₁₃ < i
                        && c[x₁₄] == a[i₁₃])
                || (exists i₁₃: int ::
                        a[i₁₃] == b[i₁₃]
                        && i₁₃ < 100000
                        && x₁₄ == i₁₃
                        && old(i) <= i₁₃
                        && i₁₃ < i
                        && c[x₁₄] == a[i₁₃])))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
            )
               ==> c[x₁₄] == old(c[x₁₄])))
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000));
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
      invariant true
        && old(x) <= x
        && x <= 100000
        && (forall x₁₉: int ::
              (  old(x) <= x₁₉
                && x₁₉ < x
                 ==> x₁₉ < 100000));
    {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₂₁: int ::
            (  old(x) <= x₂₁
              && x₂₁ < x
               ==> x₂₁ < 100000));
  {
    assert a[x] == c[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

