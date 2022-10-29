type state;

function P(s: state): bool;
function Q(s: state): bool;
function I(s: state, s: state): bool;
function R(s: state, s: state): bool;

function d(s: state): int;
function t(s: state): bool;
function B(s: state, s: state): bool;

procedure loop()
{
    var s: state;
    assume P(s);

    while(t(s))
        decreases d(s);
        invariant I(old(s), s);
        summary   R(old(s), s);
    {
        var s_: state;
        assume B(s, s_);
        s := s_;
    }

    assert Q(s);
}