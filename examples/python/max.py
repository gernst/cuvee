from help_methods import requires, ensures, out


def max(x, y):
    requires(type(x) == int and type(y) == int and x > 0)
    ensures(out() >= x)
    ensures(out() >= y)
    if (x >= y):
        return x
    else:
        return y
