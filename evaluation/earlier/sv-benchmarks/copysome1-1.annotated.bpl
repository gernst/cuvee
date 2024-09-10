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
  var a1: [int]int;
  var a2: [int]int;
  var i: int;
  var z: int;
  z := 150000;
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant old(i) <= i
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> (exists nondet_int₁₅: int, nondet_int₂₆: int ::
                      -2147483648 <= nondet_int₂₆
                      && nondet_int₂₆ < 2147483648
                      && -2147483648 <= nondet_int₁₅
                      && nondet_int₁₅ < 2147483648
                      && i₇ < 200000
                      && a1[i₇] == nondet_int₁₅
                      && a2[i₇] == nondet_int₂₆)))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> a1[i₇] == old(a1)[i₇]
                && a2[i₇] == old(a2)[i₇]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a1[i] := nondet_int₁;
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    a2[i] := nondet_int₂;
    i := i + 1;
  }
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ != z
                  && i₁₁ < 200000
                  && a2[i₁₁] == a1[i₁₁]
                ||   i₁₁ == z
                  && i₁₁ < 200000))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> a2[i₁₁] == old(a2)[i₁₁]));
  {
    if(i != z) {
      a2[i] := a1[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 200000)
    decreases 200000 - x;
    invariant old(x) <= x
      && (forall x₁₅: int ::
            (  old(x) <= x₁₅
              && x₁₅ < x
               ==> x₁₅ != z
                  && x₁₅ < 200000
                ||   x₁₅ == z
                  && x₁₅ < 200000));
  {
    if(x != z) {
      assert a1[x] == a2[x];
    }
    x := x + 1;
  }
  c#result := 0;
  return;
}

