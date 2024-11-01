data nat = zero | succ(pred: nat);

function not_(p: bool): bool;
axiom not_(false) == true;
axiom not_(true) == false;

function and_(p: bool, q: bool): bool;
axiom forall q: bool ::
    and_(false, q) == false;
axiom forall q: bool ::
    and_(true, q) == q;

function or_(p: bool, q: bool): bool;
axiom forall q: bool ::
    or_(false, q) == q;
axiom forall q: bool ::
    or_(true, q) == true;

function imp_(p: bool, q: bool): bool;
axiom forall q: bool ::
    imp_(false, q) == true;
axiom forall q: bool ::
    imp_(true, q) == q;

// deMorgan's laws are not discovered with fusion of only two functions
lemma forall p: bool, q: bool ::
    not_(and_(p, q)) == or_(not_(p), not_(q));
lemma forall p: bool, q: bool ::
    not_(or_(p, q)) == and_(not_(p), not_(q));

data prop
  = T | F | Atom(index: nat)
  | Not(phi: prop)
  | And(psi1: prop, psi2: prop)
  | Or (chi1: prop, chi2: prop)
  ;

function Imp(p: prop, q: prop): prop { Or(Not(p), q) }

function eval(v: [nat]bool, p: prop): bool;

axiom forall v: [nat]bool ::
    eval(v, T) == true;
axiom forall v: [nat]bool ::
    eval(v, F) == false;
axiom forall v: [nat]bool, i: nat ::
    eval(v, Atom(i)) == v[i];
axiom forall v: [nat]bool, p: prop ::
    eval(v, Not(p)) == not_(eval(v, p));
axiom forall v: [nat]bool, p: prop, q: prop ::
    eval(v, And(p, q)) == and_(eval(v, p), eval(v, q));
axiom forall v: [nat]bool, p: prop, q: prop ::
    eval(v, Or(p, q)) == or_(eval(v, p), eval(v, q));

function Not_(p: prop): prop;
// function And_(p: prop, q: prop): prop { And(p, q) }
// function Or_(p: prop, q: prop): prop { Or(p, q) }

axiom Not_(T) == F;
axiom Not_(F) == T;
axiom forall index: nat ::
    Not_(Atom(index)) == Not(Atom(index));
axiom forall p: prop ::
    Not_(Not(p)) == p;
axiom forall p: prop, q: prop ::
    Not_(And(p, q)) == Not(And(p, q));
axiom forall p: prop, q: prop ::
    Not_(Or(p, q)) == Not(Or(p, q));

function simplify(p: prop): prop;
axiom simplify(T) == T;
axiom simplify(F) == F;
axiom forall index: nat ::
    simplify(Atom(index)) == Atom(index);
axiom forall p: prop ::
    simplify(Not(p)) == Not_(simplify(p));
axiom forall p: prop, q: prop ::
    simplify(And(p, q)) == And(simplify(p), simplify(q));
axiom forall p: prop, q: prop ::
    simplify(Or(p, q)) == Or(simplify(p), simplify(q));