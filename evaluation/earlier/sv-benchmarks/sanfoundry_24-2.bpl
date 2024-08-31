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
    invariant true
      && old(i) <= i
      && i <= num
      && (forall x₇: int ::
            ((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
               ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                      i₆ < num
                      && x₇ == i₆
                      && old(i) <= i₆
                      && i₆ < i
                      && array[x₇] == __VERIFIER_nondet_int₂₅)))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
            )
               ==> array[x₇] == old(array[x₇])))
      && (forall i₆: int ::
            (  old(i₆) <= i₆
              && old(i) <= i₆
              && i₆ < i
               ==> i₆ < num));
  {
    var __VERIFIER_nondet_int₂: int;
    array := array[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < num)
    decreases num - i;
    invariant true
      && old(i) <= i
      && i <= num
      && (forall i₁₁: int ::
            (  old(i₁₁) <= i₁₁
              && old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < num));
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
    invariant true
      && old(i) <= i
      && i <= num
      && (forall i₁₄: int ::
            (  old(i₁₄) <= i₁₄
              && old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < num));
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

