from help_methods import requires, ensures, out


def abs(x):
    requires(type(x) == int)
    ensures(out() >= 0)

    if (x < 0):
        return -x
    else:
        return x
