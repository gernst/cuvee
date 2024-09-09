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
  var j: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> (exists __VERIFIER_nondet_int₁₃: int ::
                      i₄ < 100000
                      && b[i₄] == __VERIFIER_nondet_int₁₃)))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> b[i₄] == old(b)[i₄]));
  {
    var __VERIFIER_nondet_int₁: int;
    b := b[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 1;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(j) <= j
      && (forall i₇: int, j₈: int ::
            (  old(j) <= j₈
              && j₈ < j
               ==> i₇ < 100000
                && a[j₈] == b[i₇]))
      && (forall j₈: int ::
            (!(  old(j) <= j₈
              && j₈ < j
            )
               ==> a[j₈] == old(a)[j₈]));
  {
    a := a[j := b[i]];
    i := i + 4;
    j := j + 1;
  }
  i := 1;
  j := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(j) <= j
      && (forall i₁₂: int, j₁₃: int ::
            (  old(j) <= j₁₃
              && j₁₃ < j
               ==> i₁₂ < 100000));
  {
    assert a[j] == b[4 * j + 1];
    i := i + 4;
    j := j + 1;
  }
  c#result := 0;
  return;
}

