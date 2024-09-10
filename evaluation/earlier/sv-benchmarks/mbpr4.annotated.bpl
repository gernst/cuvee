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
    var CCCELVOL4: int := 5;
    var CCCELVOL3: int := 7;
    var CCCELVOL2: int := 3;
    var CCCELVOL1: int := 1;
    if(CELLCOUNT % 4 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 4 == 0;
    i := 1;
    while(i <= CELLCOUNT / 4)
      decreases CELLCOUNT / 4 + 1 - i;
      invariant old(i) <= i
        && (forall i₄: int ::
              (  old(i) <= i₄
                && i₄ < i
                 ==> MINVAL <= CCCELVOL4
                    && i₄ <= CELLCOUNT / 4
                    && volArray[-4 + 4 * i₄] == CCCELVOL4
                  ||   !(MINVAL <= CCCELVOL4
                    )
                    && i₄ <= CELLCOUNT / 4
                    && volArray[-4 + 4 * i₄] == 0))
        && (forall i₄: int ::
              (!(  old(i) <= i₄
                && i₄ < i
              )
                 ==> volArray[-4 + 4 * i₄] == old(volArray)[-4 + 4 * i₄]));
    {
      if(MINVAL <= CCCELVOL4) {
        volArray[((i * 4) - 4)] := CCCELVOL4;
      } else {
        volArray[((i * 4) - 4)] := 0;
      }
      volArray[((i * 4) - 3)] := volArray[i * 4 - 3];
      volArray[((i * 4) - 2)] := volArray[i * 4 - 2];
      volArray[((i * 4) - 1)] := volArray[i * 4 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 4)
      decreases CELLCOUNT / 4 + 1 - i;
      invariant old(i) <= i
        && (forall i₇: int ::
              (  old(i) <= i₇
                && i₇ < i
                 ==> MINVAL <= CCCELVOL3
                    && i₇ <= CELLCOUNT / 4
                    && volArray[-3 + 4 * i₇] == CCCELVOL3
                  ||   !(MINVAL <= CCCELVOL3
                    )
                    && i₇ <= CELLCOUNT / 4
                    && volArray[-3 + 4 * i₇] == 0))
        && (forall i₇: int ::
              (!(  old(i) <= i₇
                && i₇ < i
              )
                 ==> volArray[-3 + 4 * i₇] == old(volArray)[-3 + 4 * i₇]));
    {
      if(MINVAL <= CCCELVOL3) {
        volArray[((i * 4) - 3)] := CCCELVOL3;
      } else {
        volArray[((i * 4) - 3)] := 0;
      }
      volArray[((i * 4) - 4)] := volArray[i * 4 - 4];
      volArray[((i * 4) - 2)] := volArray[i * 4 - 2];
      volArray[((i * 4) - 1)] := volArray[i * 4 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 4)
      decreases CELLCOUNT / 4 + 1 - i;
      invariant old(i) <= i
        && (forall i₁₀: int ::
              (  old(i) <= i₁₀
                && i₁₀ < i
                 ==> MINVAL <= CCCELVOL2
                    && i₁₀ <= CELLCOUNT / 4
                    && volArray[-2 + 4 * i₁₀] == CCCELVOL2
                  ||   !(MINVAL <= CCCELVOL2
                    )
                    && i₁₀ <= CELLCOUNT / 4
                    && volArray[-2 + 4 * i₁₀] == 0))
        && (forall i₁₀: int ::
              (!(  old(i) <= i₁₀
                && i₁₀ < i
              )
                 ==> volArray[-2 + 4 * i₁₀] == old(volArray)[-2 + 4 * i₁₀]));
    {
      if(MINVAL <= CCCELVOL2) {
        volArray[((i * 4) - 2)] := CCCELVOL2;
      } else {
        volArray[((i * 4) - 2)] := 0;
      }
      volArray[((i * 4) - 4)] := volArray[i * 4 - 4];
      volArray[((i * 4) - 3)] := volArray[i * 4 - 3];
      volArray[((i * 4) - 1)] := volArray[i * 4 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 4)
      decreases CELLCOUNT / 4 + 1 - i;
      invariant old(i) <= i
        && (forall i₁₃: int ::
              (  old(i) <= i₁₃
                && i₁₃ < i
                 ==> MINVAL <= CCCELVOL1
                    && i₁₃ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₁₃] == CCCELVOL1
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && i₁₃ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₁₃] == 0))
        && (forall i₁₃: int ::
              (!(  old(i) <= i₁₃
                && i₁₃ < i
              )
                 ==> volArray[-1 + 4 * i₁₃] == old(volArray)[-1 + 4 * i₁₃]));
    {
      if(MINVAL <= CCCELVOL1) {
        volArray[((i * 4) - 1)] := CCCELVOL1;
      } else {
        volArray[((i * 4) - 1)] := 0;
      }
      volArray[((i * 4) - 4)] := volArray[i * 4 - 4];
      volArray[((i * 4) - 3)] := volArray[i * 4 - 3];
      volArray[((i * 4) - 2)] := volArray[i * 4 - 2];
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant old(i) <= i
        && (forall i₁₆: int ::
              (  old(i) <= i₁₆
                && i₁₆ < i
                 ==> i₁₆ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

