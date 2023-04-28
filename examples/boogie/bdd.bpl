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

function branch(x: int, left: node, right: node): node {
    if(left == right)
    then left
    else Node(x, left, right)
}

function neg(n: node): node;
axiom neg(False) == True;
axiom neg(True)  == False;
axiom forall x: int, l: node, r: node ::
    neg(Node(x, l, r)) == branch(x, neg(l), neg(r));

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
           then branch(mx, conj(ml, Node(nx, nl, nr)), conj(mr, Node(nx, nl, nr)))
           else if(mx > nx)
           then branch(nx, conj(Node(mx, ml, mr), nl), conj(Node(mx, ml, mr), nr))
           else branch(mx, conj(ml, nl), conj(mr, nr));


// this function gives a meaning to BDDs,
// taking an interpretation v from variables to truth values (a functional map)

function eval(n: node, v: [int]bool): bool;
axiom forall v: [int]bool ::
    eval(False, v) == false;
axiom forall v: [int]bool ::
    eval(True, v) == true;
axiom forall v: [int]bool, x: int, l: node, r: node ::
    eval(Node(x, l, r), v) == if v[x] then eval(l, v) else eval(r, v);

// Task 3 b: correctness of disjunction
lemma forall n: node, v: [int]bool ::
    eval(neg(n), v) == (!eval(n, v))
proof induction n;

// Task 3 a: correctness of conjunction
lemma forall m: node, n: node, v: [int]bool ::
    eval(conj(m, n), v) == (eval(m, v) && eval(n, v))
proof induction m {
    case Node(mx, ml, mr) =>
        induction n // nested induction
};

function sorted(a: [int]int): bool {
    forall i: int, j: int ::
        i < j ==> a[i] < a[j]
}

// Ordered BDDs are formalized by mapping variables to a strongly monotonic counter (via arrays a).
function ordered(u: int, a: [int]int, n: node): bool;

axiom forall u: int, a: [int]int ::
    ordered(u, a, False);
axiom forall u: int, a: [int]int ::
    ordered(u, a, True);
axiom forall u: int, a: [int]int, x: int, l: node, r: node ::
    ordered(u, a, Node(x, l, r))
        == (u < a[x] && ordered(a[x], a, l) && ordered(a[x], a, r));


// this is a helper lemma --- it is a bit suspicous that it goes through without induction,
// but it seems that it sufficies to unroll ordered once only
lemma forall a: [int]int, u: int, w: int, n: node ::
    sorted(a) && ordered(u, a, n) && w <= u
        ==> ordered(w, a, n);

// Task 4 a:
lemma forall a: [int]int, u: int, n: node ::
    sorted(a) && ordered(u, a, n)
        ==> ordered(u, a, neg(n))
proof induction n;

// Task 4 b:
lemma forall a: [int]int, u: int, m: node, n: node ::
    sorted(a) && ordered(u, a, m) && ordered(u, a, n)
        ==> ordered(u, a, conj(m, n))
proof induction m {
    case Node(mx, ml, mr) =>
        induction n {
            case Node(nx, nl, nr) =>
                auto // TODO: this fails
        }
};