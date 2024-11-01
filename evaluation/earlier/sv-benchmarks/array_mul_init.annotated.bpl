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
  var k: int;
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < 100000
                && a[i₅] == i₅
                && b[i₅] == i₅))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]
                && b[i₅] == old(b)[i₅]));
  {
    a[i] := i;
    b[i] := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> (exists nondet_short₂₉: int, k₁₀: int ::
                        -32768 <= k₁₀
                        && k₁₀ < 32768
                        && nondet_short₂₉ != 0
                        && -32768 <= nondet_short₂₉
                        && nondet_short₂₉ < 32768
                        && i₁₂ < 100000
                        && a[i₁₂] == k₁₀
                        && b[i₁₂] == k₁₀ * k₁₀)
                || (exists nondet_short₂₉: int ::
                        nondet_short₂₉ == 0
                        && -32768 <= nondet_short₂₉
                        && nondet_short₂₉ < 32768
                        && i₁₂ < 100000)))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> a[i₁₂] == old(a)[i₁₂]
                && b[i₁₂] == old(b)[i₁₂]));
  {
    var nondet_short₂: int;
    assume -32768 <= nondet_short₂ && nondet_short₂ < 32768;
    if(nondet_short₂ != 0) {
      havoc k;
      assume -32768 <= k && k < 32768;
      a[i] := k;
      b[i] := k * k;
    }
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 100000));
  {
    assert a[i] == b[i] || b[i] == a[i] * a[i];
    i := i + 1;
  }
}

