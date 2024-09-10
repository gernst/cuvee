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
    var CCCELVOL5: int := 8;
    var CCCELVOL4: int := 5;
    var CCCELVOL3: int := 7;
    var CCCELVOL2: int := 3;
    var CCCELVOL1: int := 1;
    if(CELLCOUNT % 5 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 5 == 0;
    i := 1;
    while(i <= CELLCOUNT / 5) {
      if(MINVAL <= CCCELVOL5) {
        volArray[((i * 5) - 5)] := CCCELVOL5;
      } else {
        volArray[((i * 5) - 5)] := 0;
      }
      volArray[((i * 5) - 4)] := volArray[i * 5 - 4];
      volArray[((i * 5) - 3)] := volArray[i * 5 - 3];
      volArray[((i * 5) - 2)] := volArray[i * 5 - 2];
      volArray[((i * 5) - 1)] := volArray[i * 5 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 5) {
      if(MINVAL <= CCCELVOL4) {
        volArray[((i * 5) - 4)] := CCCELVOL4;
      } else {
        volArray[((i * 5) - 4)] := 0;
      }
      volArray[((i * 5) - 5)] := volArray[i * 5 - 5];
      volArray[((i * 5) - 3)] := volArray[i * 5 - 3];
      volArray[((i * 5) - 2)] := volArray[i * 5 - 2];
      volArray[((i * 5) - 1)] := volArray[i * 5 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 5) {
      if(MINVAL <= CCCELVOL3) {
        volArray[((i * 5) - 3)] := CCCELVOL3;
      } else {
        volArray[((i * 5) - 3)] := 0;
      }
      volArray[((i * 5) - 5)] := volArray[i * 5 - 5];
      volArray[((i * 5) - 4)] := volArray[i * 5 - 4];
      volArray[((i * 5) - 2)] := volArray[i * 5 - 2];
      volArray[((i * 5) - 1)] := volArray[i * 5 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 5) {
      if(MINVAL <= CCCELVOL2) {
        volArray[((i * 5) - 2)] := CCCELVOL2;
      } else {
        volArray[((i * 5) - 2)] := 0;
      }
      volArray[((i * 5) - 5)] := volArray[i * 5 - 5];
      volArray[((i * 5) - 4)] := volArray[i * 5 - 4];
      volArray[((i * 5) - 3)] := volArray[i * 5 - 3];
      volArray[((i * 5) - 1)] := volArray[i * 5 - 1];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 5) {
      if(MINVAL <= CCCELVOL1) {
        volArray[((i * 5) - 1)] := CCCELVOL1;
      } else {
        volArray[((i * 5) - 1)] := 0;
      }
      volArray[((i * 5) - 5)] := volArray[i * 5 - 5];
      volArray[((i * 5) - 4)] := volArray[i * 5 - 4];
      volArray[((i * 5) - 3)] := volArray[i * 5 - 3];
      volArray[((i * 5) - 2)] := volArray[i * 5 - 2];
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

