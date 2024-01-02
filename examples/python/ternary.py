from help_methods import requires, ensures, out


def ter(x, y):
    requires(type(x) == int)
    requires(type(y) == int)
    ensures(out() == y if x == 0 else out() == x)
    if x == 0:
        return y
    else:
        return x
