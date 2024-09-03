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
      invariant true
        && 1 <= i
        && i <= 1 + CELLCOUNT / 4
        && (forall x₅: int ::
              ((exists i₄: int ::
                    if(x₅ == -1 + 4 * i₄) then 1 <= i₄ && i₄ < i else if(x₅ == -2 + 4 * i₄) then 1 <= i₄ && i₄ < i else if(x₅ == -3 + 4 * i₄) then 1 <= i₄ && i₄ < i else x₅ == -4 + 4 * i₄ && 1 <= i₄ && i₄ < i)
                 ==> (exists i₄: int ::
                          MINVAL <= CCCELVOL4
                          && i₄ <= CELLCOUNT / 4
                          && if(x₅ == -1 + 4 * i₄) then 1 <= i₄ && i₄ < i && volArray[x₅] == volArray[-4 + 4 * i₄ := CCCELVOL4][-3 + 4 * i₄ := volArray[-4 + 4 * i₄ := CCCELVOL4][-3 + 4 * i₄]][-2 + 4 * i₄ := volArray[-4 + 4 * i₄ := CCCELVOL4][-3 + 4 * i₄ := volArray[-4 + 4 * i₄ := CCCELVOL4][-3 + 4 * i₄]][-2 + 4 * i₄]][-1 + 4 * i₄] else if(x₅ == -2 + 4 * i₄) then 1 <= i₄ && i₄ < i && volArray[x₅] == volArray[-4 + 4 * i₄ := CCCELVOL4][-3 + 4 * i₄ := volArray[-4 + 4 * i₄ := CCCELVOL4][-3 + 4 * i₄]][-2 + 4 * i₄] else if(x₅ == -3 + 4 * i₄) then 1 <= i₄ && i₄ < i && volArray[x₅] == volArray[-4 + 4 * i₄ := CCCELVOL4][-3 + 4 * i₄] else x₅ == -4 + 4 * i₄ && 1 <= i₄ && i₄ < i && volArray[x₅] == CCCELVOL4)
                  || (exists i₄: int ::
                          !(MINVAL <= CCCELVOL4
                          )
                          && i₄ <= CELLCOUNT / 4
                          && if(x₅ == -1 + 4 * i₄) then 1 <= i₄ && i₄ < i && volArray[x₅] == volArray[-4 + 4 * i₄ := 0][-3 + 4 * i₄ := volArray[-4 + 4 * i₄ := 0][-3 + 4 * i₄]][-2 + 4 * i₄ := volArray[-4 + 4 * i₄ := 0][-3 + 4 * i₄ := volArray[-4 + 4 * i₄ := 0][-3 + 4 * i₄]][-2 + 4 * i₄]][-1 + 4 * i₄] else if(x₅ == -2 + 4 * i₄) then 1 <= i₄ && i₄ < i && volArray[x₅] == volArray[-4 + 4 * i₄ := 0][-3 + 4 * i₄ := volArray[-4 + 4 * i₄ := 0][-3 + 4 * i₄]][-2 + 4 * i₄] else if(x₅ == -3 + 4 * i₄) then 1 <= i₄ && i₄ < i && volArray[x₅] == volArray[-4 + 4 * i₄ := 0][-3 + 4 * i₄] else x₅ == -4 + 4 * i₄ && 1 <= i₄ && i₄ < i && volArray[x₅] == 0)))
        && (forall x₅: int ::
              (!((exists i₄: int ::
                    if(x₅ == -1 + 4 * i₄) then 1 <= i₄ && i₄ < i else if(x₅ == -2 + 4 * i₄) then 1 <= i₄ && i₄ < i else if(x₅ == -3 + 4 * i₄) then 1 <= i₄ && i₄ < i else x₅ == -4 + 4 * i₄ && 1 <= i₄ && i₄ < i)
              )
                 ==> volArray[x₅] == old(volArray[x₅])))
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i
                 ==> i₄ <= CELLCOUNT / 4));
    {
      if(MINVAL <= CCCELVOL4) {
        volArray := volArray[i * 4 - 4 := CCCELVOL4];
      } else {
        volArray := volArray[i * 4 - 4 := 0];
      }
      volArray := volArray[i * 4 - 3 := volArray[i * 4 - 3]];
      volArray := volArray[i * 4 - 2 := volArray[i * 4 - 2]];
      volArray := volArray[i * 4 - 1 := volArray[i * 4 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 4)
      decreases CELLCOUNT / 4 + 1 - i;
      invariant true
        && 1 <= i
        && i <= 1 + CELLCOUNT / 4
        && (forall x₉: int ::
              ((exists i₈: int ::
                    if(x₉ == -1 + 4 * i₈) then 1 <= i₈ && i₈ < i else if(x₉ == -2 + 4 * i₈) then 1 <= i₈ && i₈ < i else if(x₉ == -4 + 4 * i₈) then 1 <= i₈ && i₈ < i else x₉ == -3 + 4 * i₈ && 1 <= i₈ && i₈ < i)
                 ==> (exists i₈: int ::
                          MINVAL <= CCCELVOL3
                          && i₈ <= CELLCOUNT / 4
                          && if(x₉ == -1 + 4 * i₈) then 1 <= i₈ && i₈ < i && volArray[x₉] == volArray[-3 + 4 * i₈ := CCCELVOL3][-4 + 4 * i₈ := volArray[-3 + 4 * i₈ := CCCELVOL3][-4 + 4 * i₈]][-2 + 4 * i₈ := volArray[-3 + 4 * i₈ := CCCELVOL3][-4 + 4 * i₈ := volArray[-3 + 4 * i₈ := CCCELVOL3][-4 + 4 * i₈]][-2 + 4 * i₈]][-1 + 4 * i₈] else if(x₉ == -2 + 4 * i₈) then 1 <= i₈ && i₈ < i && volArray[x₉] == volArray[-3 + 4 * i₈ := CCCELVOL3][-4 + 4 * i₈ := volArray[-3 + 4 * i₈ := CCCELVOL3][-4 + 4 * i₈]][-2 + 4 * i₈] else if(x₉ == -4 + 4 * i₈) then 1 <= i₈ && i₈ < i && volArray[x₉] == volArray[-3 + 4 * i₈ := CCCELVOL3][-4 + 4 * i₈] else x₉ == -3 + 4 * i₈ && 1 <= i₈ && i₈ < i && volArray[x₉] == CCCELVOL3)
                  || (exists i₈: int ::
                          !(MINVAL <= CCCELVOL3
                          )
                          && i₈ <= CELLCOUNT / 4
                          && if(x₉ == -1 + 4 * i₈) then 1 <= i₈ && i₈ < i && volArray[x₉] == volArray[-3 + 4 * i₈ := 0][-4 + 4 * i₈ := volArray[-3 + 4 * i₈ := 0][-4 + 4 * i₈]][-2 + 4 * i₈ := volArray[-3 + 4 * i₈ := 0][-4 + 4 * i₈ := volArray[-3 + 4 * i₈ := 0][-4 + 4 * i₈]][-2 + 4 * i₈]][-1 + 4 * i₈] else if(x₉ == -2 + 4 * i₈) then 1 <= i₈ && i₈ < i && volArray[x₉] == volArray[-3 + 4 * i₈ := 0][-4 + 4 * i₈ := volArray[-3 + 4 * i₈ := 0][-4 + 4 * i₈]][-2 + 4 * i₈] else if(x₉ == -4 + 4 * i₈) then 1 <= i₈ && i₈ < i && volArray[x₉] == volArray[-3 + 4 * i₈ := 0][-4 + 4 * i₈] else x₉ == -3 + 4 * i₈ && 1 <= i₈ && i₈ < i && volArray[x₉] == 0)))
        && (forall x₉: int ::
              (!((exists i₈: int ::
                    if(x₉ == -1 + 4 * i₈) then 1 <= i₈ && i₈ < i else if(x₉ == -2 + 4 * i₈) then 1 <= i₈ && i₈ < i else if(x₉ == -4 + 4 * i₈) then 1 <= i₈ && i₈ < i else x₉ == -3 + 4 * i₈ && 1 <= i₈ && i₈ < i)
              )
                 ==> volArray[x₉] == old(volArray[x₉])))
        && (forall i₈: int ::
              (  1 <= i₈
                && i₈ < i
                 ==> i₈ <= CELLCOUNT / 4));
    {
      if(MINVAL <= CCCELVOL3) {
        volArray := volArray[i * 4 - 3 := CCCELVOL3];
      } else {
        volArray := volArray[i * 4 - 3 := 0];
      }
      volArray := volArray[i * 4 - 4 := volArray[i * 4 - 4]];
      volArray := volArray[i * 4 - 2 := volArray[i * 4 - 2]];
      volArray := volArray[i * 4 - 1 := volArray[i * 4 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 4)
      decreases CELLCOUNT / 4 + 1 - i;
      invariant true
        && 1 <= i
        && i <= 1 + CELLCOUNT / 4
        && (forall x₁₃: int ::
              ((exists i₁₂: int ::
                    if(x₁₃ == -1 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i else if(x₁₃ == -3 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i else if(x₁₃ == -4 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i else x₁₃ == -2 + 4 * i₁₂ && 1 <= i₁₂ && i₁₂ < i)
                 ==> (exists i₁₂: int ::
                          MINVAL <= CCCELVOL2
                          && i₁₂ <= CELLCOUNT / 4
                          && if(x₁₃ == -1 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-2 + 4 * i₁₂ := CCCELVOL2][-4 + 4 * i₁₂ := volArray[-2 + 4 * i₁₂ := CCCELVOL2][-4 + 4 * i₁₂]][-3 + 4 * i₁₂ := volArray[-2 + 4 * i₁₂ := CCCELVOL2][-4 + 4 * i₁₂ := volArray[-2 + 4 * i₁₂ := CCCELVOL2][-4 + 4 * i₁₂]][-3 + 4 * i₁₂]][-1 + 4 * i₁₂] else if(x₁₃ == -3 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-2 + 4 * i₁₂ := CCCELVOL2][-4 + 4 * i₁₂ := volArray[-2 + 4 * i₁₂ := CCCELVOL2][-4 + 4 * i₁₂]][-3 + 4 * i₁₂] else if(x₁₃ == -4 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-2 + 4 * i₁₂ := CCCELVOL2][-4 + 4 * i₁₂] else x₁₃ == -2 + 4 * i₁₂ && 1 <= i₁₂ && i₁₂ < i && volArray[x₁₃] == CCCELVOL2)
                  || (exists i₁₂: int ::
                          !(MINVAL <= CCCELVOL2
                          )
                          && i₁₂ <= CELLCOUNT / 4
                          && if(x₁₃ == -1 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-2 + 4 * i₁₂ := 0][-4 + 4 * i₁₂ := volArray[-2 + 4 * i₁₂ := 0][-4 + 4 * i₁₂]][-3 + 4 * i₁₂ := volArray[-2 + 4 * i₁₂ := 0][-4 + 4 * i₁₂ := volArray[-2 + 4 * i₁₂ := 0][-4 + 4 * i₁₂]][-3 + 4 * i₁₂]][-1 + 4 * i₁₂] else if(x₁₃ == -3 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-2 + 4 * i₁₂ := 0][-4 + 4 * i₁₂ := volArray[-2 + 4 * i₁₂ := 0][-4 + 4 * i₁₂]][-3 + 4 * i₁₂] else if(x₁₃ == -4 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-2 + 4 * i₁₂ := 0][-4 + 4 * i₁₂] else x₁₃ == -2 + 4 * i₁₂ && 1 <= i₁₂ && i₁₂ < i && volArray[x₁₃] == 0)))
        && (forall x₁₃: int ::
              (!((exists i₁₂: int ::
                    if(x₁₃ == -1 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i else if(x₁₃ == -3 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i else if(x₁₃ == -4 + 4 * i₁₂) then 1 <= i₁₂ && i₁₂ < i else x₁₃ == -2 + 4 * i₁₂ && 1 <= i₁₂ && i₁₂ < i)
              )
                 ==> volArray[x₁₃] == old(volArray[x₁₃])))
        && (forall i₁₂: int ::
              (  1 <= i₁₂
                && i₁₂ < i
                 ==> i₁₂ <= CELLCOUNT / 4));
    {
      if(MINVAL <= CCCELVOL2) {
        volArray := volArray[i * 4 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 4 - 2 := 0];
      }
      volArray := volArray[i * 4 - 4 := volArray[i * 4 - 4]];
      volArray := volArray[i * 4 - 3 := volArray[i * 4 - 3]];
      volArray := volArray[i * 4 - 1 := volArray[i * 4 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 4)
      decreases CELLCOUNT / 4 + 1 - i;
      invariant true
        && 1 <= i
        && i <= 1 + CELLCOUNT / 4
        && (forall x₁₇: int ::
              ((exists i₁₆: int ::
                    if(x₁₇ == -2 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i else if(x₁₇ == -3 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i else if(x₁₇ == -4 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i else x₁₇ == -1 + 4 * i₁₆ && 1 <= i₁₆ && i₁₆ < i)
                 ==> (exists i₁₆: int ::
                          MINVAL <= CCCELVOL1
                          && i₁₆ <= CELLCOUNT / 4
                          && if(x₁₇ == -2 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-1 + 4 * i₁₆ := CCCELVOL1][-4 + 4 * i₁₆ := volArray[-1 + 4 * i₁₆ := CCCELVOL1][-4 + 4 * i₁₆]][-3 + 4 * i₁₆ := volArray[-1 + 4 * i₁₆ := CCCELVOL1][-4 + 4 * i₁₆ := volArray[-1 + 4 * i₁₆ := CCCELVOL1][-4 + 4 * i₁₆]][-3 + 4 * i₁₆]][-2 + 4 * i₁₆] else if(x₁₇ == -3 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-1 + 4 * i₁₆ := CCCELVOL1][-4 + 4 * i₁₆ := volArray[-1 + 4 * i₁₆ := CCCELVOL1][-4 + 4 * i₁₆]][-3 + 4 * i₁₆] else if(x₁₇ == -4 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-1 + 4 * i₁₆ := CCCELVOL1][-4 + 4 * i₁₆] else x₁₇ == -1 + 4 * i₁₆ && 1 <= i₁₆ && i₁₆ < i && volArray[x₁₇] == CCCELVOL1)
                  || (exists i₁₆: int ::
                          !(MINVAL <= CCCELVOL1
                          )
                          && i₁₆ <= CELLCOUNT / 4
                          && if(x₁₇ == -2 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-1 + 4 * i₁₆ := 0][-4 + 4 * i₁₆ := volArray[-1 + 4 * i₁₆ := 0][-4 + 4 * i₁₆]][-3 + 4 * i₁₆ := volArray[-1 + 4 * i₁₆ := 0][-4 + 4 * i₁₆ := volArray[-1 + 4 * i₁₆ := 0][-4 + 4 * i₁₆]][-3 + 4 * i₁₆]][-2 + 4 * i₁₆] else if(x₁₇ == -3 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-1 + 4 * i₁₆ := 0][-4 + 4 * i₁₆ := volArray[-1 + 4 * i₁₆ := 0][-4 + 4 * i₁₆]][-3 + 4 * i₁₆] else if(x₁₇ == -4 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-1 + 4 * i₁₆ := 0][-4 + 4 * i₁₆] else x₁₇ == -1 + 4 * i₁₆ && 1 <= i₁₆ && i₁₆ < i && volArray[x₁₇] == 0)))
        && (forall x₁₇: int ::
              (!((exists i₁₆: int ::
                    if(x₁₇ == -2 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i else if(x₁₇ == -3 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i else if(x₁₇ == -4 + 4 * i₁₆) then 1 <= i₁₆ && i₁₆ < i else x₁₇ == -1 + 4 * i₁₆ && 1 <= i₁₆ && i₁₆ < i)
              )
                 ==> volArray[x₁₇] == old(volArray[x₁₇])))
        && (forall i₁₆: int ::
              (  1 <= i₁₆
                && i₁₆ < i
                 ==> i₁₆ <= CELLCOUNT / 4));
    {
      if(MINVAL <= CCCELVOL1) {
        volArray := volArray[i * 4 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 4 - 1 := 0];
      }
      volArray := volArray[i * 4 - 4 := volArray[i * 4 - 4]];
      volArray := volArray[i * 4 - 3 := volArray[i * 4 - 3]];
      volArray := volArray[i * 4 - 2 := volArray[i * 4 - 2]];
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant true
        && 0 <= i
        && i <= CELLCOUNT
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i
                 ==> i₂₀ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

