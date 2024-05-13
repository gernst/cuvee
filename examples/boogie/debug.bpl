const A: bool;
const B: bool;

goal
  !(A && !B)
    ==> !A || B;