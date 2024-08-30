type key;
type value;
data alist = nil | acons(key: key, value: value, tail: alist);

function contains(a: key, xs: alist): bool;
function get(a: key, xs: alist): value;
function put(a: key, v: value, xs: alist): value;

axiom forall a: key ::
  contains(a, nil) == false;
axiom forall a: key, b: key, v: value, xs: alist ::
  contains(a, acons(b, v, xs)) == (a == b || contains (a, xs));

axiom forall a: key, b: key, v: value, xs: alist ::
  get(a, acons(b, v, xs)) == if a == b then v else get(a, xs);