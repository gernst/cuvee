const A: bool;
const B: bool;
const C: bool;

goal A ==> A;
goal A ==> B;
goal A ==> A && B;
goal B ==> A && B;
goal A && B ==> A && B;
goal A && A;
goal A && A ==> B;

const c: int;
function P(x: int): bool;
function Q(x: int, y: int): bool;

// ok to substitute all of these!
goal forall x: int :: x == c ==> P(x);
goal forall x: int :: x == c && P(x);
goal exists x: int :: x == c && P(x);
goal exists x: int :: x == c ==> P(x);

// TODO: so far does not substitute
goal forall x: int :: P(x) && x == c;
goal exists x: int :: P(x) && x == c;