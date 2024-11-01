data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var CELLCOUNT: int;

procedure main()
  returns (c#result: int)
  modifies CELLCOUNT;
{
  CELLCOUNT := 0;
  havoc CELLCOUNT;
  assume -2147483648 <= CELLCOUNT && CELLCOUNT < 2147483648;
  if(1 < CELLCOUNT) {
    var MINVAL: int := 2;
    var i: int;
    var volArray: [int]int;
    var CCCELVOL3: int := 7;
    var CCCELVOL2: int := 3;
    var CCCELVOL1: int := 1;
    if(CELLCOUNT % 3 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 3 == 0;
    i := 1;
    while(i <= CELLCOUNT / 3)
      decreases CELLCOUNT / 3 + 1 - i;
      invariant old(i) <= i
        && (forall i₄: int ::
              (  old(i) <= i₄
                && i₄ < i
                 ==> MINVAL <= CCCELVOL3
                    && i₄ <= CELLCOUNT / 3
                    && volArray[-3 + 3 * i₄] == CCCELVOL3
                  ||   !(MINVAL <= CCCELVOL3
                    )
                    && i₄ <= CELLCOUNT / 3
                    && volArray[-3 + 3 * i₄] == 0))
        && (forall i₄: int ::
              (!(  old(i) <= i₄
                && i₄ < i
              )
                 ==> volArray[-3 + 3 * i₄] == old(volArray)[-3 + 3 * i₄]));
    {
      if(MINVAL <= CCCELVOL3) {
        volArray[((i * 3) - 3)] := CCCELVOL3;
      } else {
        volArray[((i * 3) - 3)] := 0;
      }
      volArray[((i * 3) - 2)] := volArray[i * 3 - 2];
      volArray[((i * 3) - 1)] := volArray[i * 3 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 3)
      decreases CELLCOUNT / 3 + 1 - i;
      invariant old(i) <= i
        && (forall i₇: int ::
              (  old(i) <= i₇
                && i₇ < i
                 ==> MINVAL <= CCCELVOL2
                    && i₇ <= CELLCOUNT / 3
                    && volArray[-2 + 3 * i₇] == CCCELVOL2
                  ||   !(MINVAL <= CCCELVOL2
                    )
                    && i₇ <= CELLCOUNT / 3
                    && volArray[-2 + 3 * i₇] == 0))
        && (forall i₇: int ::
              (!(  old(i) <= i₇
                && i₇ < i
              )
                 ==> volArray[-2 + 3 * i₇] == old(volArray)[-2 + 3 * i₇]));
    {
      if(MINVAL <= CCCELVOL2) {
        volArray[((i * 3) - 2)] := CCCELVOL2;
      } else {
        volArray[((i * 3) - 2)] := 0;
      }
      volArray[((i * 3) - 3)] := volArray[i * 3 - 3];
      volArray[((i * 3) - 1)] := volArray[i * 3 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 3)
      decreases CELLCOUNT / 3 + 1 - i;
      invariant old(i) <= i
        && (forall i₁₀: int ::
              (  old(i) <= i₁₀
                && i₁₀ < i
                 ==> MINVAL <= CCCELVOL1
                    && i₁₀ <= CELLCOUNT / 3
                    && volArray[-1 + 3 * i₁₀] == CCCELVOL1
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && i₁₀ <= CELLCOUNT / 3
                    && volArray[-1 + 3 * i₁₀] == 0))
        && (forall i₁₀: int ::
              (!(  old(i) <= i₁₀
                && i₁₀ < i
              )
                 ==> volArray[-1 + 3 * i₁₀] == old(volArray)[-1 + 3 * i₁₀]));
    {
      if(MINVAL <= CCCELVOL1) {
        volArray[((i * 3) - 1)] := CCCELVOL1;
      } else {
        volArray[((i * 3) - 1)] := 0;
      }
      volArray[((i * 3) - 2)] := volArray[i * 3 - 2];
      volArray[((i * 3) - 3)] := volArray[i * 3 - 3];
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant old(i) <= i
        && (forall i₁₃: int ::
              (  old(i) <= i₁₃
                && i₁₃ < i
                 ==> i₁₃ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

