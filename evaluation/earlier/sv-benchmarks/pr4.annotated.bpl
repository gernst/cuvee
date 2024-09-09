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
        && (forall i₅: int ::
              (  old(i) <= i₅
                && i₅ < i
                 ==> MINVAL <= CCCELVOL1
                    && MINVAL <= CCCELVOL2
                    && MINVAL <= CCCELVOL3
                    && MINVAL <= CCCELVOL4
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == CCCELVOL1
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == CCCELVOL2)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == CCCELVOL3)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == CCCELVOL4)
                  ||   MINVAL <= CCCELVOL1
                    && MINVAL <= CCCELVOL2
                    && MINVAL <= CCCELVOL3
                    && !(MINVAL <= CCCELVOL4
                    )
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == CCCELVOL1
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == CCCELVOL2)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == CCCELVOL3)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == 0)
                  ||   MINVAL <= CCCELVOL1
                    && MINVAL <= CCCELVOL2
                    && !(MINVAL <= CCCELVOL3
                    )
                    && MINVAL <= CCCELVOL4
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == CCCELVOL1
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == CCCELVOL2)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == 0)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == CCCELVOL4)
                  ||   MINVAL <= CCCELVOL1
                    && MINVAL <= CCCELVOL2
                    && !(MINVAL <= CCCELVOL3
                    )
                    && !(MINVAL <= CCCELVOL4
                    )
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == CCCELVOL1
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == CCCELVOL2)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == 0)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == 0)
                  ||   MINVAL <= CCCELVOL1
                    && !(MINVAL <= CCCELVOL2
                    )
                    && MINVAL <= CCCELVOL3
                    && MINVAL <= CCCELVOL4
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == CCCELVOL1
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == 0)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == CCCELVOL3)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == CCCELVOL4)
                  ||   MINVAL <= CCCELVOL1
                    && !(MINVAL <= CCCELVOL2
                    )
                    && MINVAL <= CCCELVOL3
                    && !(MINVAL <= CCCELVOL4
                    )
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == CCCELVOL1
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == 0)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == CCCELVOL3)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == 0)
                  ||   MINVAL <= CCCELVOL1
                    && !(MINVAL <= CCCELVOL2
                    )
                    && !(MINVAL <= CCCELVOL3
                    )
                    && MINVAL <= CCCELVOL4
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == CCCELVOL1
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == 0)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == 0)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == CCCELVOL4)
                  ||   MINVAL <= CCCELVOL1
                    && !(MINVAL <= CCCELVOL2
                    )
                    && !(MINVAL <= CCCELVOL3
                    )
                    && !(MINVAL <= CCCELVOL4
                    )
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == CCCELVOL1
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == 0)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == 0)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == 0)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && MINVAL <= CCCELVOL2
                    && MINVAL <= CCCELVOL3
                    && MINVAL <= CCCELVOL4
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == 0
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == CCCELVOL2)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == CCCELVOL3)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == CCCELVOL4)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && MINVAL <= CCCELVOL2
                    && MINVAL <= CCCELVOL3
                    && !(MINVAL <= CCCELVOL4
                    )
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == 0
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == CCCELVOL2)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == CCCELVOL3)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == 0)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && MINVAL <= CCCELVOL2
                    && !(MINVAL <= CCCELVOL3
                    )
                    && MINVAL <= CCCELVOL4
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == 0
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == CCCELVOL2)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == 0)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == CCCELVOL4)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && MINVAL <= CCCELVOL2
                    && !(MINVAL <= CCCELVOL3
                    )
                    && !(MINVAL <= CCCELVOL4
                    )
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == 0
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == CCCELVOL2)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == 0)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == 0)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && !(MINVAL <= CCCELVOL2
                    )
                    && MINVAL <= CCCELVOL3
                    && MINVAL <= CCCELVOL4
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == 0
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == 0)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == CCCELVOL3)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == CCCELVOL4)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && !(MINVAL <= CCCELVOL2
                    )
                    && MINVAL <= CCCELVOL3
                    && !(MINVAL <= CCCELVOL4
                    )
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == 0
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == 0)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == CCCELVOL3)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == 0)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && !(MINVAL <= CCCELVOL2
                    )
                    && !(MINVAL <= CCCELVOL3
                    )
                    && MINVAL <= CCCELVOL4
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == 0
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == 0)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == 0)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == CCCELVOL4)
                  ||   !(MINVAL <= CCCELVOL1
                    )
                    && !(MINVAL <= CCCELVOL2
                    )
                    && !(MINVAL <= CCCELVOL3
                    )
                    && !(MINVAL <= CCCELVOL4
                    )
                    && i₅ <= CELLCOUNT / 4
                    && volArray[-1 + 4 * i₅] == 0
                    && (-2 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-2 + 4 * i₅] == 0)
                    && (  -3 + 4 * i₅ != -2 + 4 * i₅
                      && -3 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-3 + 4 * i₅] == 0)
                    && (  -4 + 4 * i₅ != -3 + 4 * i₅
                      && -4 + 4 * i₅ != -2 + 4 * i₅
                      && -4 + 4 * i₅ != -1 + 4 * i₅
                       ==> volArray[-4 + 4 * i₅] == 0)));
    {
      if(MINVAL <= CCCELVOL4) {
        volArray := volArray[i * 4 - 4 := CCCELVOL4];
      } else {
        volArray := volArray[i * 4 - 4 := 0];
      }
      if(MINVAL <= CCCELVOL3) {
        volArray := volArray[i * 4 - 3 := CCCELVOL3];
      } else {
        volArray := volArray[i * 4 - 3 := 0];
      }
      if(MINVAL <= CCCELVOL2) {
        volArray := volArray[i * 4 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 4 - 2 := 0];
      }
      if(MINVAL <= CCCELVOL1) {
        volArray := volArray[i * 4 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 4 - 1 := 0];
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

