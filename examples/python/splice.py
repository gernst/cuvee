from help_methods import requires, ensures, out


def splice(a, b):
    requires(type(a) == list)
    requires(type(b) == list)
    requires(len(a) >= 3)
    ensures(out() == a)
    # ensures(len(out()) == 1)
    # a[1] = 44
    b = a[1:]

    return a[:2] + a[2:]
