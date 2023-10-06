data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function foldr(f: [nat][nat]nat, z: nat, xs: list): nat;
axiom forall f: [nat][nat]nat, z: nat ::
    foldr(f, z, nil) == z;
axiom forall f: [nat][nat]nat, z: nat, x: nat, xs: list ::
    foldr(f, z, cons(x, xs)) == f[x][foldr(f, z, xs)];

function foldl(f: [nat][nat]nat, z: nat, xs: list): nat;
axiom forall f: [nat][nat]nat, z: nat ::
    foldl(f, z, nil) == z;
axiom forall f: [nat][nat]nat, z: nat, x: nat, xs: list ::
    foldl(f, z, cons(x, xs)) == foldl(f, f[x][z], xs);