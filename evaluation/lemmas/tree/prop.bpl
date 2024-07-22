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

data prop
  = T | F | Atom(index: nat)
  | Not(phi: prop)
  | And(psi1: prop, psi2: prop)
  | Or (chi1: prop, chi2: prop)
  ;

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

// just cancels negation
function neg(p: prop): prop;
axiom neg(T) == F;
axiom neg(F) == T;
axiom forall i: nat ::
    neg(Atom(i)) == Not(Atom(i));
axiom forall p: prop ::
    neg(Not(p)) == p;
axiom forall p: prop, q: prop ::
    neg(And(p, q)) == Not(And(p, q));
axiom forall p: prop, q: prop ::
    neg(Or(p, q)) == Not(Or(p, q));

function nnf(p: prop): prop;
axiom nnf(T) == T;
axiom nnf(F) == F;
axiom nnf(Not(T)) == F;
axiom nnf(Not(F)) == T;

axiom forall i: nat ::
    nnf(Not(Atom(i))) == Not(Atom(i));
axiom forall p: prop ::
    nnf(Not(Not(p))) == nnf(p);
axiom forall p: prop, q: prop ::
    nnf(Not(And(p, q))) == Or(neg(nnf(p)), neg(nnf(q)));
axiom forall p: prop, q: prop ::
    nnf(Not(Or(p, q))) == And(neg(nnf(p)), neg(nnf(q)));

axiom forall i: nat ::
    nnf(Atom(i)) == Atom(i);
axiom forall p: prop, q: prop ::
    nnf(And(p, q)) == And(nnf(p), nnf(q));
axiom forall p: prop, q: prop ::
    nnf(Or(p, q)) == Or(nnf(p), nnf(q));

// lemma forall v: [nat]bool, p: prop ::
//     eval(v, neg(p)) == (not_eval(v, p))
// proof induction p;

<<<<<<< HEAD
axiom forall v: [nat]bool, p: prop ::
    eval(v, neg(p)) == not_(eval(v, p));


function simplify(p: prop): prop;

axiom forall p: prop ::
    simplify(Not(p)) = snot(simplify(p));

axiom forall p: prop, q: prop ::
    simplify(And(p, q)) = And(p, q);


function snot(p: prop): prop;

axiom
    snot(T) = F;
axiom forall p: prop ::
    snot(Not(p)) = p;
axiom forall p: prop, q: prop ::
    snot(And(p, q)) = Not(And(p, q));
=======
lemma forall v: [nat]bool, p: prop ::
    eval(v, nnf(p)) == eval(v, p)
proof induction p {
    case Not(phi) =>
        induction phi
};

function Not_(p: prop): prop;
function And_(p: prop, q: prop): prop { And(p, q) }
function Or_(p: prop, q: prop): prop { Or(p, q) }

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
>>>>>>> main
