from help_methods import requires, ensures, out


def in_(a):
    requires(type(a) == list)
    requires(len(a) > 3)
    ensures(0 in out())
    a[1] = 0
    return a[:2]
