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
    while(i <= CELLCOUNT / 4) {
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
    while(i <= CELLCOUNT / 4) {
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
    while(i <= CELLCOUNT / 4) {
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
    while(i <= CELLCOUNT / 4) {
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
    while(i < CELLCOUNT) {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

