data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure printEven(i: int)
  returns (c#result: c#void)
{
  assert i % 2 == 0;
}

procedure printOdd(i: int)
  returns (c#result: c#void)
{
  assert i % 2 != 0;
}

procedure main()
  returns (c#result: int)
{
  var array: [int]int;
  var i: int;
  var num: int;
  assume -2147483648 <= num && num < 2147483648;
  i := 0;
  while(i < num)
    decreases num - i;
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> (exists nondet_int₁₄: int ::
                      -2147483648 <= nondet_int₁₄
                      && nondet_int₁₄ < 2147483648
                      && i₅ < num
                      && array[i₅] == nondet_int₁₄)))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> array[i₅] == old(array)[i₅]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    array[i] := nondet_int₁;
    i := i + 1;
  }
  i := 0;
  while(i < num)
    decreases num - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> array[i₉] % 2 == 0
                  && i₉ < num
                ||   array[i₉] % 2 != 0
                  && i₉ < num));
  {
    if(array[i] % 2 == 0) {
      var printEven₃: c#void;
      printEven₃ := call printEven(array[i]);
    }
    i := i + 1;
  }
  i := 0;
  while(i < num)
    decreases num - i;
    invariant old(i) <= i
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> array[i₁₂] % 2 != 0
                  && i₁₂ < num
                ||   array[i₁₂] % 2 == 0
                  && i₁₂ < num));
  {
    if(array[i] % 2 != 0) {
      var printOdd₅: c#void;
      printOdd₅ := call printOdd(array[i]);
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

