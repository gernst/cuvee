from cuvee import out, ensures, requires


def if_true(a):
    requires(type(a) == bool)
    ensures(out() == a)
    if (True):
        return a
    return not a
