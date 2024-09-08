data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var CELLCOUNT: int;

procedure main()
  returns (c#result: int)
  modifies CELLCOUNT;
{
  havoc CELLCOUNT;
  if(1 < CELLCOUNT) {
    var MINVAL: int := 2;
    var i: int;
    var volArray: [int]int;
    var CCCELVOL2: int := 3;
    var CCCELVOL1: int := 1;
    if(CELLCOUNT % 2 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 2 == 0;
    i := 1;
    while(i <= CELLCOUNT / 2)
      decreases CELLCOUNT / 2 + 1 - i;
      invariant old(i) <= i
        && i <= 1 + CELLCOUNT / 2
        && (forall i₄: int ::
              (  old(i) <= i₄
                && i₄ < i
                 ==> MINVAL <= CCCELVOL2
                    && i₄ <= CELLCOUNT / 2
                    && volArray[-2 + 2 * i₄] == CCCELVOL2
                  ||   !(MINVAL <= CCCELVOL2
                    )
                    && i₄ <= CELLCOUNT / 2
                    && volArray[-2 + 2 * i₄] == 0))
        && (forall i₄: int ::
              (!(  old(i) <= i₄
                && i₄ < i
              )
                 ==> volArray[-2 + 2 * i₄] == old(volArray)[-2 + 2 * i₄]));
    {
      if(MINVAL <= CCCELVOL2) {
        volArray := volArray[i * 2 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 2 - 2 := 0];
      }
      volArray := volArray[i * 2 - 1 := volArray[i * 2 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 2)
      decreases CELLCOUNT / 2 + 1 - i;
      invariant old(i) <= i
        && i <= 1 + CELLCOUNT / 2
        && (forall i₇: int ::
              (  old(i) <= i₇
                && i₇ < i
                 ==> MINVAL <= CCCELVOL1
                    && i₇ <= CELLCOUNT / 2
                    && volArray[-1 + 2 * i₇] == CCCELVOL1
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && i₇ <= CELLCOUNT / 2
                    && volArray[-1 + 2 * i₇] == 0))
        && (forall i₇: int ::
              (!(  old(i) <= i₇
                && i₇ < i
              )
                 ==> volArray[-1 + 2 * i₇] == old(volArray)[-1 + 2 * i₇]));
    {
      if(MINVAL <= CCCELVOL1) {
        volArray := volArray[i * 2 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 2 - 1 := 0];
      }
      volArray := volArray[i * 2 - 2 := volArray[i * 2 - 2]];
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant old(i) <= i
        && i <= CELLCOUNT
        && (forall i₁₀: int ::
              (  old(i) <= i₁₀
                && i₁₀ < i
                 ==> i₁₀ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

