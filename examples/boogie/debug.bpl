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

function eval_nnf(v: [nat]bool, p: prop): bool;

axiom forall x₀ : [nat]bool ::
    eval_nnf(x₀, T) == true;

axiom forall x₀ : [nat]bool ::
    eval_nnf(x₀, F) == false;

axiom forall x₀ : [nat]bool ::
    eval_nnf(x₀, Not(T)) == false;

axiom forall x₀ : [nat]bool ::
    eval_nnf(x₀, Not(F)) == true;

axiom forall x₀ : [nat]bool, i: nat ::
    eval_nnf(x₀, Not(Atom(i))) == not_(x₀[i]);

axiom forall x₀ : [nat]bool, p: prop ::
    eval_nnf(x₀, Not(Not(p))) == eval_nnf(x₀, p);

axiom forall x₀ : [nat]bool, p: prop, q: prop ::
    eval_nnf(x₀, Not(And(p, q))) == or_(not_(eval_nnf(x₀, p)), not_(eval_nnf(x₀, q)));

axiom forall x₀ : [nat]bool, p: prop, q: prop ::
    eval_nnf(x₀, Not(Or(p, q))) == and_(not_(eval_nnf(x₀, p)), not_(eval_nnf(x₀, q)));

axiom forall x₀ : [nat]bool, i: nat ::
    eval_nnf(x₀, Atom(i)) == x₀[i];

axiom forall x₀ : [nat]bool, p: prop, q: prop ::
    eval_nnf(x₀, And(p, q)) == and_(eval_nnf(x₀, p), eval_nnf(x₀, q));

axiom forall x₀ : [nat]bool, p: prop, q: prop ::
    eval_nnf(x₀, Or(p, q)) == or_(eval_nnf(x₀, p), eval_nnf(x₀, q));

lemma forall v: [nat]bool, p: prop, q: prop ::
    not_(or_(eval(v, p), eval(v, q))) == and_(not_(eval(v, p)), not_(eval(v, q)));

lemma forall v: [nat]bool, p: prop, q: prop ::
    not_(and_(eval(v, p), eval(v, q))) == or_(not_(eval(v, p)), not_(eval(v, q)));