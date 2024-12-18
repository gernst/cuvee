data term
  = o | up(inner: term) | lam(body: term) | app(fun: term, arg: term);

data subst
  = id | shift(that: subst) | push(base: subst, top: term);

function apply(m: term, s: subst): term;
function compose(s: subst, t: subst): subst;

axiom forall m: term ::
  apply(m, id)
    == m;

axiom forall m: term, s: subst ::
  apply(m, shift(s))
    == up(apply(m, s));

axiom forall s: subst, p: term ::
  apply(o, push(s, p))
    == p;

axiom forall m: term, s: subst, p: term ::
  apply(up(m), push(s, p))
    == apply(m, s);

axiom forall m: term, s: subst, p: term ::
  apply(lam(m), push(s, p))
    == lam(apply(m, push(shift(push(s, p)), o)));

axiom forall m: term, n: term, s: subst, p: term ::
  apply(app(m, n), push(s, p))
    == app(apply(m, push(s, p)), apply(n, push(s, p)));


axiom forall s: subst ::
  compose(s, id)
    == s;

axiom forall s: subst, t: subst ::
  compose(s, shift(t))
    == shift(compose(s, t));

axiom forall t: subst, p: term ::
  compose(id, push(t, p))
    == push(t, p);

axiom forall s: subst, m: term, t: subst, p: term ::
  compose(push(s, m), push(t, p))
    == push(compose(s, push(t, p)),
            apply(m, push(t, p)));

axiom forall s: subst, t: subst, p: term ::
  compose(shift(s), push(t, p))
    == compose(s, t);