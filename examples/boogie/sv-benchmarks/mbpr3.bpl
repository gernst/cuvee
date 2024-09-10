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
    while(i <= CELLCOUNT / 3) {
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
    while(i <= CELLCOUNT / 3) {
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
    while(i <= CELLCOUNT / 3) {
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
    while(i < CELLCOUNT) {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

