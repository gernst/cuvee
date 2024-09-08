data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

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
  var __VERIFIER_nondet_int₁: int;
  var num: int;
  num := __VERIFIER_nondet_int₁;
  i := 0;
  while(i < num)
    decreases num - i;
    invariant old(i) <= i
      && i <= num
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> (exists __VERIFIER_nondet_int₂₅: int ::
                      i₆ < num
                      && array[i₆] == __VERIFIER_nondet_int₂₅)))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> array[i₆] == old(array)[i₆]));
  {
    var __VERIFIER_nondet_int₂: int;
    array := array[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < num)
    decreases num - i;
    invariant old(i) <= i
      && i <= num
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> array[i₁₀] % 2 == 0
                  && i₁₀ < num
                ||   array[i₁₀] % 2 != 0
                  && i₁₀ < num));
  {
    if(array[i] % 2 == 0) {
      var printEven₄: c#void;
      printEven₄ := call printEven(array[i]);
    }
    i := i + 1;
  }
  i := 0;
  while(i < num)
    decreases num - i;
    invariant old(i) <= i
      && i <= num
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> array[i₁₃] % 2 != 0
                  && i₁₃ < num
                ||   array[i₁₃] % 2 == 0
                  && i₁₃ < num));
  {
    if(array[i] % 2 != 0) {
      var printOdd₆: c#void;
      printOdd₆ := call printOdd(array[i]);
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

