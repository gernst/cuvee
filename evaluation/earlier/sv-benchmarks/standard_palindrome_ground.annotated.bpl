data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var A: [int]int;
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> (exists __VERIFIER_nondet_int₁₃: int ::
                      i₄ < 100000
                      && A[i₄] == __VERIFIER_nondet_int₁₃)))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> A[i₄] == old(A)[i₄]));
  {
    var __VERIFIER_nondet_int₁: int;
    A := A[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < 100000 / 2)
    decreases 100000 / 2 - i;
    invariant old(i) <= i
      && i <= 100000 / 2
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < 100000 / 2
                && A[i₇] == old(A)[99999 + -i₇]))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> A[i₇] == old(A)[i₇]));
  {
    A := A[i := A[100000 - i - 1]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000 / 2)
    decreases 100000 / 2 - x;
    invariant old(x) <= x
      && x <= 100000 / 2
      && (forall x₁₁: int ::
            (  old(x) <= x₁₁
              && x₁₁ < x
               ==> x₁₁ < 100000 / 2));
  {
    assert A[x] == A[100000 - x - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}

