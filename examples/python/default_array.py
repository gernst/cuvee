from help_methods import requires, ensures, out


def ar(a):
    requires(type(a) == list)
    ensures(len(out()) == 3)
    ensures(out()[0] == 5)
    ensures(out()[1] == 8)
    ensures(out()[2] == 13)
    a = [5, 8, 13]
    return a
