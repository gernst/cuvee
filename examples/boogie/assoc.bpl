type key;
type value;
data alist = nil | acons(key: key, value: value, tail: alist);

const true_: bool { true }
const false_: bool { false }

function eq_key(key1: key, key2: key): bool { key1 == key2 }

function ite_bool(test: bool, left: bool, right: bool): bool {
  if test then left else right
}

function ite_value(test: bool, left: value, right: value): value {
  if test then left else right
}

function contains(a: key, xs: alist): bool;
function get(a: key, xs: alist): value;
function put(a: key, v: value, xs: alist): value;

axiom forall a: key ::
  contains(a, nil) == false;
axiom forall a: key, b: key, v: value, xs: alist ::
  contains(a, acons(b, v, xs)) == (a == b || contains (a, xs));

