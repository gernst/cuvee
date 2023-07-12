from help_methods import requires, ensures, out


def con(a, b):
    requires(type(a) == list)
    requires(type(b) == list)
    requires(len(a) > 0)
    requires(len(b) > 0)
    # ensures(forall(out()[0:len(a)], lambda x: out()[x] == a[x]))
    # ensures(forall(b, lambda y: out()[y+len(a)] == b[y]))
    ensures(out()[0:len(a)] == a)
    ensures(out()[len(a):len(a)+len(b)] == b)
    return a + b
