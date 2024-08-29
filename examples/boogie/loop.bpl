type state;

function P(s: state): bool;
function Q(s: state, s_: state): bool;
function I(s: state, s_: state): bool;
function R(s: state, s_: state): bool;

function d(s: state): int;
function t(s: state): bool;
function b(s: state): bool;
function A(s: state, s: state): bool;
function B(s: state, s: state): bool;

procedure loop(s: state)
    returns (s_: state)
    requires P(s);
    ensures Q(s, s_);
{
    while(t(s))
        decreases d(s);
        invariant I(old(s), s);
        summary   R(s, final(s));
    {
        var s_: state;
        assume B(s, s_);
        s := s_;
        if(!b(s_)) { break; }
    }

    s_ := s;
}