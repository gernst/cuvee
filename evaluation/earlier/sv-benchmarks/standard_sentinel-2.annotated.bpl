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
  var __VERIFIER_nondet_int₁: int;
  var marker: int;
  marker := __VERIFIER_nondet_int₁;
  var __VERIFIER_nondet_int₂: int;
  var pos: int;
  pos := __VERIFIER_nondet_int₂;
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₃₆: int, i₇: int ::
                      i₇ < 100000
                      && x₈ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && a[x₈] == __VERIFIER_nondet_int₃₆)))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> a[x₈] == old(a[x₈])))
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < 100000));
  {
    var __VERIFIER_nondet_int₃: int;
    a := a[i := __VERIFIER_nondet_int₃];
    i := i + 1;
  }
  if(0 <= pos && pos < 100000) {
    a := a[pos := marker];
    var i: int := 0;
    while(a[i] != marker)
      invariant true
        && old(i) <= i
        && (forall i₁₁: int ::
              (  old(i) <= i₁₁
                && i₁₁ < i
                 ==> a[i₁₁] != marker));
    {
      i := i + 1;
    }
    assert i <= pos;
  }
  c#result := 0;
  return;
}

