data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var __VERIFIER_nondet_int₁: int;
  var j: int;
  j := __VERIFIER_nondet_int₁;
  var __VERIFIER_nondet_int₂: int;
  var n: int;
  n := __VERIFIER_nondet_int₂;
  assume n < 100000;
  var a: [int]int;
  assume 0 < j && j < 10000;
  i := 1;
  while(i < n)
    decreases n - i;
    invariant true
      && old(i) <= i
      && i <= n
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists __VERIFIER_nondet_int₃₇: int, i₉: int ::
                      0 < __VERIFIER_nondet_int₃₇
                      && __VERIFIER_nondet_int₃₇ < 10000
                      && i₉ < n
                      && x₁₀ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && a[x₁₀] == i₉ + j + __VERIFIER_nondet_int₃₇)))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < n));
  {
    var __VERIFIER_nondet_int₃: int;
    var k: int;
    k := __VERIFIER_nondet_int₃;
    assume 0 < k && k < 10000;
    a := a[i := i + j + k];
    i := i + 1;
  }
  i := 1;
  while(i < n)
    decreases n - i;
    invariant true
      && old(i) <= i
      && i <= n
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < n));
  {
    assert i + 2 <= a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

