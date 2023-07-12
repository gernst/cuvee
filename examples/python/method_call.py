from help_methods import requires, ensures, out, termination


def add(x, y):
    requires(type(x) == int and type(y) == int)
    requires(x >= 0)
    ensures(out() == x + y)
    ensures(type(out()) == int)
    while (x > 0):
        requires(type(x) == int)
        requires(type(y) == int)
        requires(x >= 0)
        ensures(y == x + y)
        ensures(type(y) == int)
        termination(x)
        x = x - 1
        y = y + 1
    return y


def mean(x, y):
    requires(type(x) == int and type(y) == int)
    requires(x >= 0 and y >= 0)
    ensures(out() == (x + y) // 2)
    s = add(x, y)
    return s // 2
