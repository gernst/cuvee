const c: int;
function P(x: int): bool;
function Q(x: int, y: int): bool;

goal forall x: int :: x == c && P(x);
goal forall x: int :: P(x) && x == c;