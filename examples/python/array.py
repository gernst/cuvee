from help_methods import requires, ensures, out


def array(a):
    requires(type(a) == list)
    requires(len(a) >= 1)
    ensures(out()[0] == 0)
    a[0] = 0
    return a
