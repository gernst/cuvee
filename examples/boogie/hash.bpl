type key;
type value;

data option<a>
  = none | some(the: a);

data pair<a,b>
  = pair(fst: a, snd: b);

data list<a>
  = nil | cons(head: a, tail: list<a>);

const ainit: list<pair<key,value>>;
function acontains(k: key, m: list<pair<key,value>>): bool;
function aget(k: key, m: list<pair<key,value>>): option<value>;
function aput(k: key, v: value, m: list<pair<key,value>>): list<pair<key,value>>;
function adel(k: key, m: list<pair<key,value>>): list<pair<key,value>>;

axiom
  ainit == nil;

axiom forall k: key ::
  acontains(k, nil)
    == false;
axiom forall k: key, k_: key, v_: value, m: list<pair<key,value>> ::
  acontains(k, cons(pair(k_, v_), m))
    == if k == k_ then true else acontains(k, m);

axiom forall k: key ::
  aget(k, nil)
    == none;
axiom forall k: key, k_: key, v_: value, m: list<pair<key,value>> ::
  aget(k, cons(pair(k_, v_), m))
    == if k == k_ then some(v_) else aget(k, m);

axiom forall k: key, v: value ::
  aput(k, v, nil)
    == cons(pair(k, v), nil);
axiom forall k: key, v: value, k_: key, v_: value, m: list<pair<key,value>> ::
  aput(k, v, cons(pair(k_, v_), m))
    == if k == k_ then cons(pair(k, v), m) else cons(pair(k_, v_), aput(k, v, m));

axiom forall k: key ::
  adel(k, nil)
    == nil;
axiom forall k: key, k_: key, v_: value, m: list<pair<key,value>> ::
  adel(k, cons(pair(k_, v_), m))
    == if k == k_ then adel(k, m) else cons(pair(k_, v_), adel(k, m));

function hash(key: key): int;
