type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

// Declarations of functions

function eq(xs: list<elem>, ys: list<elem>): bool;
axiom
  eq(nil, nil) == true;
axiom forall y: elem, ys: list<elem> ::
  eq(nil, cons(y, ys)) == false;
axiom forall x: elem, xs: list<elem> ::
  eq(cons(x, xs), nil) == false;
axiom forall x: elem, xs: list<elem>, y: elem, ys: list<elem> ::
  eq(cons(x, xs), cons(y, ys)) == (x == y && eq(xs, ys));

function length(xs: list<elem>): int;
function contains(x: elem, xs: list<elem>): bool;
function count(x: elem, xs: list<elem>): int;
function snoc(xs: list<elem>, x: elem): list<elem>;
function rotate(cnt: int, xs: list<elem>): list<elem>;
function take(cnt: int, xs: list<elem>): list<elem>;
function drop(cnt: int, xs: list<elem>): list<elem>;
function reverse(xs: list<elem>): list<elem>;
function reverseaccumulator(xs: list<elem>, ys: list<elem>): list<elem>;
function append(xs: list<elem>, ys: list<elem>): list<elem>;
function remove(x: elem, xs: list<elem>): list<elem>;

// Axioms describing the functions declared above

// length
axiom
  length(nil) == 0;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == length(xs) + 1;


// contains
axiom forall x: elem ::
  contains(x, nil) == false;
axiom forall x: elem, y: elem, ys: list<elem> ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

// count
axiom forall x: elem ::
  count(x, nil) == 0;
axiom forall x: elem, y: elem, ys: list<elem> ::
  count(x, cons(y, ys)) == ite(x == y, count(x, ys) + 1, count(x, ys));

// snoc
axiom forall z: elem ::
  snoc(nil, z) == cons(z, nil);
axiom forall z: elem, y: elem, ys: list<elem> ::
  snoc(cons(y, ys), z) == cons(y, snoc(ys, z));

// rotate
axiom forall n: int ::
  rotate(n, nil) == nil;
axiom forall n: int, y: elem, ys: list<elem> ::
  rotate(n, cons(y, ys)) == ite(n <= 0, cons(y, ys), snoc(rotate(n-1, ys), y));

// take
axiom forall n: int ::
  take(n, nil) == nil;
axiom forall n: int, y: elem, ys: list<elem> ::
  take(n, cons(y, ys)) == ite(n <= 0, nil, cons(y, take(n - 1, ys)));

// drop
axiom forall n: int ::
  drop(n, nil) == nil;
axiom forall n: int, y: elem, ys: list<elem> ::
  drop(n, cons(y, ys)) == ite(n <= 0, cons(y, ys), drop(n - 1, ys));

// reverse
axiom
  reverse(nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  reverse(cons(y, ys)) == snoc(reverse(ys), y);

// reverseaccumulator
axiom forall zs: list<elem> ::
  reverseaccumulator(nil, zs) == zs;
axiom forall zs: list<elem>, y: elem, ys: list<elem> ::
  reverseaccumulator(cons(y, ys), zs) == reverseaccumulator(ys, cons(y, zs));

// append
axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

// remove
axiom forall x: elem ::
  remove(x, nil) == nil;
axiom forall x: elem, y: elem, ys: list<elem> ::
  remove(x, cons(y, ys)) == ite(x == y, remove(x, ys), cons(y, remove(x, ys)));

// Proofs

lemma forall xs: list<elem> ::
  length(xs) >= 0
proof
  induction xs{
    case nil => auto
    case cons(x, xs) => auto
  };

lemma forall xs: list<elem>, ys: list<elem>, zs: list<elem> ::
  append(append(xs, ys), zs) == append(xs, append(ys, zs))
proof induction xs;

lemma forall xs: list<elem>, ys: list<elem> ::
  length(append(xs, ys)) == length(xs) + length(ys)
proof
  induction xs;

lemma forall xs: list<elem> ::
  reverse(reverse(xs)) == xs
proof
  induction xs {
    case cons(y, ys) =>
      show (forall z: elem, zs: list<elem> :: reverse(reverse(cons(z, zs))) == cons(z, reverse(reverse(zs))))
      proof show (forall z: elem, zs: list<elem> :: reverse(snoc(zs, z)) == cons(z, reverse(zs)))
           proof induction zs
  };


//proof forall n: Int, x: elem, xs: list<elem> ::
// ((append(take(n, xs), drop(n, xs)) == xs) ==> (append(take(n, cons(x, xs)), drop(n, cons(x, xs))) == cons(x, xs)))

lemma forall n: int, xs: list<elem> ::
  append(take(n, xs), drop(n, xs)) == xs
proof induction xs{
  case cons(x, xs) => split
};

