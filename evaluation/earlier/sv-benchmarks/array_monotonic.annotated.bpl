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
  var i: int;
  var a: [int]int;
  var b: [int]int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₅: int ::
              (exists nondet_int₁₄: int ::
                      nondet_int₁₄ == 10
                      && -2147483648 <= nondet_int₁₄
                      && nondet_int₁₄ < 2147483648
                      && i₅ < 100000
                      && a[i₅] == nondet_int₁₄
                      && b[i₅] == 20)
              || (exists nondet_int₁₄: int ::
                      nondet_int₁₄ != 10
                      && -2147483648 <= nondet_int₁₄
                      && nondet_int₁₄ < 2147483648
                      && i₅ < 100000
                      && a[i₅] == nondet_int₁₄));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[i] := nondet_int₁;
    if(a[i] == 10) {
      b[i] := 20;
    }
    i := i + 2;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₉: int ::
                a[i₉] == 10
                && i₉ < 100000
              ||   a[i₉] != 10
                && i₉ < 100000);
  {
    if(a[i] == 10) {
      assert b[i] == 20;
    }
    i := i + 2;
  }
}

