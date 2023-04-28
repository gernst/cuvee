// Tool: Cuvée e18f7d9a5783f0acbc59f3414e94a78bb1880791 (note: this branch is not public currently)
// Public repository: https://github.com/gernst/cuvee
// File Format: Boogie-like

// This would have been much easier in Isabelle ;)

// Purely functional version of BDDs.
// Solved:
//  - functional correctness 3a, 3b
//  - keeping the ordering 4a
// Attempted:
//  - 4b recursive case still open
// All proofs are by Z3, possibly supported by tactics if present

// The notion of being reduced does not make much sense here.
// Similarly, for memory safety.

// Termination is not proved, but all functions are structurally recursive

data node
  = True | False | Node(x: int, left: node, right: node);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

function and_(a: bool, b: bool): bool;
axiom forall b: bool :: and_(false, b) == false;
axiom forall b: bool :: and_(true,  b) == b;

function neg(n: node): node;
axiom neg(False) == True;
axiom neg(True)  == False;
axiom forall x: int, l: node, r: node ::
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
axiom forall mx: int, ml: node, mr: node,
             nx: int, nl: node, nr: node ::
    conj(Node(mx, ml, mr), Node(nx, nl, nr))
        == if(mx < nx)
           then Node(mx, conj(ml, Node(nx, nl, nr)), conj(mr, Node(nx, nl, nr)))
           else if(mx > nx)
           then Node(nx, conj(Node(mx, ml, mr), nl), conj(Node(mx, ml, mr), nr))
           else Node(mx, conj(ml, nl), conj(mr, nr));


// this function gives a meaning to BDDs,
// taking an interpretation v from variables to truth values (a functional map)

function eval(n: node, v: [int]bool): bool;
axiom forall v: [int]bool ::
    eval(False, v) == false;
axiom forall v: [int]bool ::
    eval(True, v) == true;
axiom forall v: [int]bool, x: int, l: node, r: node ::
    eval(Node(x, l, r), v) == if v[x] then eval(l, v) else eval(r, v);

// synthetic function to simulate fusion with two parameters, found by Cuv'ee already

function and_eval(n: node, v: [int]bool, b: bool): bool;

axiom forall b: bool, v: [int]bool ::
  and_eval(False, v, b) == false;
axiom forall v: [int]bool ::
  and_eval(True, v, false) == false;
axiom forall v: [int]bool ::
  and_eval(True, v, true) == true;
axiom forall b: bool, v: [int]bool, x: int, l: node, r: node ::
  v[x] ==> and_eval(Node(x, l, r), v, b) == and_eval(l, v, b);
axiom forall b: bool, v: [int]bool, x: int, l: node, r: node ::
   not(v[x]) ==> and_eval(Node(x, l, r), v, b) == and_eval(r, v, b);
