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
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 2
        && (forall x₆: int ::
              ((exists i₅: int ::
                    if(x₆ == -1 + 2 * i₅) then old(i) <= i₅ && i₅ < i else x₆ == -2 + 2 * i₅ && old(i) <= i₅ && i₅ < i)
                 ==> (exists i₅: int ::
                          MINVAL <= CCCELVOL1
                          && MINVAL <= CCCELVOL2
                          && i₅ <= CELLCOUNT / 2
                          && if(x₆ == -1 + 2 * i₅) then old(i) <= i₅ && i₅ < i && volArray[x₆] == CCCELVOL1 else x₆ == -2 + 2 * i₅ && old(i) <= i₅ && i₅ < i && volArray[x₆] == CCCELVOL2)
                  || (exists i₅: int ::
                          MINVAL <= CCCELVOL1
                          && !(MINVAL <= CCCELVOL2
                          )
                          && i₅ <= CELLCOUNT / 2
                          && if(x₆ == -1 + 2 * i₅) then old(i) <= i₅ && i₅ < i && volArray[x₆] == CCCELVOL1 else x₆ == -2 + 2 * i₅ && old(i) <= i₅ && i₅ < i && volArray[x₆] == 0)
                  || (exists i₅: int ::
                          !(MINVAL <= CCCELVOL1
                          )
                          && MINVAL <= CCCELVOL2
                          && i₅ <= CELLCOUNT / 2
                          && if(x₆ == -1 + 2 * i₅) then old(i) <= i₅ && i₅ < i && volArray[x₆] == 0 else x₆ == -2 + 2 * i₅ && old(i) <= i₅ && i₅ < i && volArray[x₆] == CCCELVOL2)
                  || (exists i₅: int ::
                          !(MINVAL <= CCCELVOL1
                          )
                          && !(MINVAL <= CCCELVOL2
                          )
                          && i₅ <= CELLCOUNT / 2
                          && if(x₆ == -1 + 2 * i₅) then old(i) <= i₅ && i₅ < i && volArray[x₆] == 0 else x₆ == -2 + 2 * i₅ && old(i) <= i₅ && i₅ < i && volArray[x₆] == 0)))
        && (forall x₆: int ::
              (!((exists i₅: int ::
                    if(x₆ == -1 + 2 * i₅) then old(i) <= i₅ && i₅ < i else x₆ == -2 + 2 * i₅ && old(i) <= i₅ && i₅ < i)
              )
                 ==> volArray[x₆] == old(volArray[x₆])))
        && (forall i₅: int ::
              (  old(i₅) <= i₅
                && old(i) <= i₅
                && i₅ < i
                 ==> i₅ <= CELLCOUNT / 2));
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
      invariant true
        && old(i) <= i
        && i <= CELLCOUNT
        && (forall i₉: int ::
              (  old(i₉) <= i₉
                && old(i) <= i₉
                && i₉ < i
                 ==> i₉ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

