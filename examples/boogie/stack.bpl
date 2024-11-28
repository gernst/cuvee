type elem;
data nat = zero | succ(pred: nat);
data option<a> = none | some(the: a);
data list<a>   = nil  | cons(head: a, tail: list<a>);

const empty: list<elem> { nil }
function top(s: list<elem>): option<elem>;
function pop(s: list<elem>): list<elem>;
function push(x: elem, s: list<elem>): list<elem>;

axiom
    top(nil) == none;
axiom forall x: elem, s: list<elem> ::
    top(cons(x, s)) == some(x);

axiom
    pop(nil) == nil;
axiom forall x: elem, s: list<elem> ::
    pop(cons(x, s)) == s;

axiom forall x: elem, s: list<elem> ::
    push(x, s) == cons(x, s);

function topn(n: nat, s: list<elem>): option<elem>;
axiom forall s: list<elem> ::
    topn(zero, s) == top(s);
axiom forall n: nat, s: list<elem> ::
    topn(succ(n), s) == topn(n, pop(s));
