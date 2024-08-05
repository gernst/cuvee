const i: int;
const j: int;
const x: int;

goal
  (x == 2*i || x == 2*i + 1) &&
  (x == 2*j || x == 2*j + 1) ==> i == j;