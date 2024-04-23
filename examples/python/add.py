from cuvee import requires, ensures, out


def add(x, y):
    requires(type(x) == int and type(y) == int)
    ensures(out() == x + y)
    return x + y
