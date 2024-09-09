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
    var MINVAL: int;
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
        && (forall i₅: int ::
              (  old(i) <= i₅
                && i₅ < i
                 ==> MINVAL <= CCCELVOL1
                    && MINVAL <= CCCELVOL2
                    && i₅ <= CELLCOUNT / 2
                    && volArray[-1 + 2 * i₅] == CCCELVOL1
                    && (-2 + 2 * i₅ != -1 + 2 * i₅
                       ==> volArray[-2 + 2 * i₅] == CCCELVOL2)
                  ||   MINVAL <= CCCELVOL1
                    && !(MINVAL <= CCCELVOL2
                    )
                    && i₅ <= CELLCOUNT / 2
                    && volArray[-1 + 2 * i₅] == CCCELVOL1
                    && (-2 + 2 * i₅ != -1 + 2 * i₅
                       ==> volArray[-2 + 2 * i₅] == 0)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && MINVAL <= CCCELVOL2
                    && i₅ <= CELLCOUNT / 2
                    && volArray[-1 + 2 * i₅] == 0
                    && (-2 + 2 * i₅ != -1 + 2 * i₅
                       ==> volArray[-2 + 2 * i₅] == CCCELVOL2)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && !(MINVAL <= CCCELVOL2
                    )
                    && i₅ <= CELLCOUNT / 2
                    && volArray[-1 + 2 * i₅] == 0
                    && (-2 + 2 * i₅ != -1 + 2 * i₅
                       ==> volArray[-2 + 2 * i₅] == 0)))
        && (forall i₅: int ::
              (!(  old(i) <= i₅
                && i₅ < i
              )
                 ==> volArray[-1 + 2 * i₅] == old(volArray)[-1 + 2 * i₅]
                  && volArray[-2 + 2 * i₅] == old(volArray)[-2 + 2 * i₅]));
    {
      if(MINVAL <= CCCELVOL2) {
        volArray := volArray[i * 2 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 2 - 2 := 0];
      }
      if(MINVAL <= CCCELVOL1) {
        volArray := volArray[i * 2 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 2 - 1 := 0];
      }
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant old(i) <= i
        && (forall i₈: int ::
              (  old(i) <= i₈
                && i₈ < i
                 ==> i₈ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

