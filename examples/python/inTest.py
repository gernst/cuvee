from help_methods import requires, ensures


def test(a, x, i):
    requires(type(a) == list)
    requires(type(x) == int)
    requires(type(i) == int)
    requires(i >= 0 and i < len(a))
    requires(a[i] == x)
    # requires(type(a[i]) == int)
    ensures(x in a)
