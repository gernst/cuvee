data list<a> = nil | cons(head: a, tail: list<a>);

data expr = num(value: int) | add(left: expr, right: expr);

data instr = push(arg: int) | plus;

function eval(e: expr): int;
function append(xs: list<instr>, ys: list<instr>): list<instr>;
function compile(e: expr): list<instr>;

function step(i: instr, st: list<int>): list<int>;
function steps(is: list<instr>, st: list<int>): list<int>;

axiom forall i: int ::
  eval(num(i)) == i;
axiom forall l: expr, r: expr ::
  eval(add(l, r)) == eval(l) + eval(r);

axiom forall ys: list<instr> ::
  append(nil, ys) == ys;
axiom forall x: instr, xs: list<instr>, ys: list<instr> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

axiom forall i: int ::
  compile(num(i)) == cons(push(i), nil);
axiom forall l: expr, r: expr ::
  compile(add(l, r)) == append(compile(l), append(compile(r), cons(plus, nil)));

axiom forall i: int, st: list<int> ::
  step(push(i), st) == cons(i, st);
axiom forall a: int, b: int, st: list<int> ::
  step(plus, cons(a, cons(b, st))) == cons(a + b, st);

axiom forall st: list<int> ::
  steps(nil, st) == st;
axiom forall i: instr, is: list<instr>, st: list<int> ::
  steps(cons(i, is), st) == steps(is, step(i, st));

function first(st: list<int>): int;
axiom first(nil) == 0;
axiom forall i: int, st: list<int> ::
  first(cons(i, st)) == i;

function run(e: expr): int;
axiom forall e: expr ::
  run(e) == first(steps(compile(e), nil));


// the key lemma is this: 
// "steps (compile e) st = (eval e#st)"
// but steps:0:compile has an accumulator that is annoying!
// we cannot match the result of steps:0:compile against the pattern of step(plus, _)

function steps_compile(e: expr, st: list<int>): list<int>;

axiom forall i: int, st: list<int> ::
  steps_compile(num(i), st)
    == cons(i, st);
axiom forall a: expr, b: expr, st: list<int> ::
  steps_compile(add(a, b), st)
    == step(plus, steps_compile(b, steps_compile(a, st)));