lemma
  forall x: int, x_: int ::
    {if(x <= x) { x := -x; }} (x == x_);

type state;

function P(s: state): bool;
function Q(s: state): bool;
function I(s: state, s: state): bool;
function R(s: state, s: state): bool;

function d(s: state): int;
function t(s: state): bool;
function B(s: state, s: state): bool;

lemma
  < var s: state;
    assume P(s);

    while(t(s))
        decreases d(s);
        invariant I(old(s), s);
        summary   R(s, final(s));
    {
        var s_: state;
        assume B(s, s_);
        s := s_;
    }
    
    assert Q(s);
    > true;