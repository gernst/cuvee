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
  var array: [int]int;
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> (exists nondet_int₁₃: int ::
                      -2147483648 <= nondet_int₁₃
                      && nondet_int₁₃ < 2147483648
                      && i₄ < 100000
                      && array[i₄] == nondet_int₁₃)))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> array[i₄] == old(array)[i₄]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    array[i] := nondet_int₁;
    i := i + 1;
  }
  var largest: int := array[0];
  i := 1;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall largest₇: int, i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> largest₇ < array[i₈]
                  && i₈ < 100000
                ||   !(largest₇ < array[i₈]
                  )
                  && i₈ < 100000));
  {
    if(largest < array[i]) {
      largest := array[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₁₂: int ::
            (  old(x) <= x₁₂
              && x₁₂ < x
               ==> x₁₂ < 100000));
  {
    assert array[x] <= largest;
    x := x + 1;
  }
  c#result := 0;
  return;
}

