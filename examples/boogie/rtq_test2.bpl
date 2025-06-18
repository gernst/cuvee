type elem;

data option<a> = none | some(get: a);
data list<a> = nil | cons(head: a, tail: list<a>);

data queue<a> = q(fst: list<a>, lst: list<a>);

function concat(xs: list<elem>, ys: list<elem>): list<elem>;
axiom forall ys: list<elem> ::
  concat(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  concat(cons(x,xs), ys) == cons(x, concat(xs, ys));

function reverse(xs: list<elem>): list<elem>;
axiom
  reverse(nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  reverse(cons(y, ys)) == concat(reverse(ys), cons(y, nil));

function hd(xs: list<elem>): option<elem>;
axiom
    hd(nil) == none;
axiom forall x: elem, xs: list<elem> ::
    hd(cons(x, xs)) == some(x);

function tl(xs: list<elem>): list<elem>;
axiom
    tl(nil) == nil;
axiom forall x: elem, xs: list<elem>::
    tl(cons(x, xs)) == xs;

//add element to end of list
function append(xs: list<elem>, z: elem ): list<elem>;
axiom forall z: elem :: 
  append(nil, z) == cons(z, nil);
axiom forall z: elem, y: elem, ys: list<elem> :: 
  append(cons(y, ys), z) == cons(y, append(ys, z));

//remove element from end of list
function remove_last(xs: list<elem>): list<elem>;
axiom remove_last(nil) == nil;
axiom forall x: elem :: 
    remove_last(cons(x,nil)) == nil;
axiom forall x: elem, xs: list<elem> :: 
    remove_last(cons(x, xs)) == cons(x, remove_last(xs));


//queue to list
function abs(q: queue<elem>): list<elem>;
axiom forall xs: list<elem>, ys: list<elem> ::
    abs(q(xs,  ys)) == concat(xs, reverse(ys));


//add element to front of queue
function skip_queue(q: queue<elem>, z: elem): queue<elem>;
axiom forall xs: list<elem>, ys: list<elem>, z: elem :: 
    skip_queue(q(xs, ys), z) == q(cons(z, xs), ys);

//add element to the end of queue
function enqueue(q: queue<elem>, z: elem): queue<elem>;
axiom forall z: elem, xs: list<elem>, ys: list<elem> ::
    enqueue(q(xs, ys), z) == q(xs, cons(z, ys));

//remove element from end of queue
function queue_last(q: queue<elem>): queue<elem>;
axiom
    queue_last(q(nil, nil)) == q(nil, nil);
axiom forall xs: list<elem>::
    queue_last(q(xs, nil)) == q(remove_last(xs), nil);
axiom forall y: elem, xs: list<elem>, ys: list<elem> ::
    queue_last(q(xs, cons(y, ys))) == q(xs, ys);

//get element from front of queue
function peek(q: queue<elem>): option<elem>;
axiom
  peek(q(nil, nil)) == none;
axiom forall ys: list<elem> ::
  peek(q(nil, ys)) == hd(reverse(ys));
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  peek(q(cons(x, xs), ys)) == some(x);

//remove element from front of queue
function dequeue(q: queue<elem>): queue<elem>;
axiom
    dequeue(q(nil, nil)) == q(nil, nil);
axiom forall ys: list<elem>::
    dequeue(q(nil, ys)) == q(nil, tl(ys));
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
    dequeue(q(cons(x, xs), ys)) == q(xs, ys);


function concat_queue(qa: queue<elem>, qb: queue<elem>) : queue<elem>;
axiom forall qa: queue<elem>, qb: queue<elem> ::
  concat_queue(qa, qb) == q(abs(qa), reverse(abs(qb)));


function reverse_queue(q: queue<elem>): queue<elem>;
axiom forall xs: list<elem>, ys: list<elem> :: 
  reverse_queue(q(xs, ys)) == q(ys, xs);


//list == queue
lemma forall q: queue<elem>, xs: list<elem>, ys:list<elem>, zs :list<elem> ::
  ((abs(q(ys, zs)) == xs) && (ys != nil && zs != nil)) ==> (xs == concat(ys, reverse(zs)))
proof induction xs{
  case nil => auto
  case cons(x, xs) => auto
};

//first elem
lemma forall q: queue<elem>, xs: list<elem> ::
  abs(q) == xs ==> hd(xs) == peek(q)
proof auto;

//add to back
lemma forall q: queue<elem>, xs : list<elem>, z: elem, ys: list<elem>, zs: list<elem> ::
  (abs(q(ys, zs)) == xs) ==> (abs(enqueue(q(ys, zs), z)) == append(xs, z))
proof induction xs{
  case nil => auto
  case cons(x, xs) => auto
};

//add to front
lemma forall q: queue<elem>, xs : list<elem>, z: elem, ys: list<elem>, zs: list<elem> ::
 (abs(q(ys, zs)) == xs) ==> (abs(skip_queue(q(ys, zs), z)) == cons(z, xs))
proof induction xs{
  case nil => auto
  case cons(x, xs) => auto
};

//remove from front
lemma forall q: queue<elem>, xs : list<elem>::
    (abs(q) == xs) ==> (abs(dequeue(q)) == remove_last(xs))
proof induction xs{
  case nil => auto
  case cons(x, xs) => auto
};

//remove from back
lemma forall q: queue<elem>, xs: list<elem> ::
    (abs(q) == xs) ==> (abs(queue_last(q)) == remove_last(xs))
proof induction xs{
  case nil => auto
  case cons(x, xs) => auto
};

//reverse
lemma forall q: queue<elem>, xs: list<elem> ::
    (abs(q) == xs) ==> (abs(reverse_queue(q))) == reverse(xs)
proof auto;


free lemma forall xs: list<elem> :: xs == reverse(reverse(xs));
//concat
lemma forall qa: queue<elem>, qb: queue<elem>, xs: list<elem>, ys: list<elem> ::
    (abs(qa) == xs) && (abs(qb) == ys) ==> concat(xs, ys) == abs(concat_queue(qa, qb))
proof induction xs;

