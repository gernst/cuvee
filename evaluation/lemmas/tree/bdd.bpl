// characteristic lemmas
//   (eval(neg(y₀), x₁) <==> not_(eval(y₀, x₁)));
//   similarly for and_ and and (seems much harder)

data nat = zero | succ(pred: nat);

function lt(m: nat, n: nat): bool;
axiom forall m: nat ::
  lt(m, zero) == false;
axiom forall n: nat ::
  lt(zero, succ(n)) == true;
axiom forall m: nat, n: nat ::
  lt(succ(m), succ(n)) == lt(m, n);

data node
  = True | False | Node(x: nat, left: node, right: node);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

function and_(a: bool, b: bool): bool;
axiom forall b: bool :: and_(false, b) == false;
axiom forall b: bool :: and_(true,  b) == b;

function neg(n: node): node;
axiom neg(False) == True;
axiom neg(True)  == False;
axiom forall x: nat, l: node, r: node ::
    neg(Node(x, l, r)) == Node(x, neg(l), neg(r));

function conj(m: node, n: node): node;
axiom forall n: node ::
    conj(True, n) == n;
axiom forall n: node ::
    conj(False, n) == False;
axiom forall m: node ::
    conj(m, True) == m;
axiom forall m: node ::
    conj(m, False) == False;
axiom forall mx: nat, ml: node, mr: node,
             nx: nat, nl: node, nr: node ::
    conj(Node(mx, ml, mr), Node(nx, nl, nr))
        == if lt(mx, nx)
           then Node(mx, conj(ml, Node(nx, nl, nr)), conj(mr, Node(nx, nl, nr)))
           else if lt(nx, mx)
           then Node(nx, conj(Node(mx, ml, mr), nl), conj(Node(mx, ml, mr), nr))
           else Node(mx, conj(ml, nl), conj(mr, nr));


// this function gives a meaning to BDDs,
// taking an naterpretation v from variables to truth values (a functional map)
function eval(n: node, v: [nat]bool): bool;
axiom forall v: [nat]bool ::
    eval(False, v) == false;
axiom forall v: [nat]bool ::
    eval(True, v) == true;
axiom forall v: [nat]bool, x: nat, l: node, r: node ::
    eval(Node(x, l, r), v) == if v[x] then eval(l, v) else eval(r, v);