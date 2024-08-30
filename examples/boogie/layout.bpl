data list<a> = nil | cons(head: a, tail: list<a>);

type char;
data pair   = pair(nesting: int, chars: list<char>);
data layout = layout(lines: list<pair>);

// this does not really work :/

function append(xs: list<pair>, ys: list<pair>): list<pair>;
axiom forall ys: list<pair> ::
    append(nil, ys) == ys;
axiom forall x: pair, xs: list<pair>, ys: list<pair> ::
    append(cons(x, xs), ys) == cons(x, append(xs, ys));

function text(s: list<char>): layout {
    layout(cons(pair(0, s), nil))
}

function nest(k: int, l: layout): layout;

function vertical(l1: layout, l2: layout): layout;
axiom forall lines1: list<pair>, lines2: list<pair> ::
    vertical(layout(lines1), layout(lines2))
        == layout(append(lines1, lines2));