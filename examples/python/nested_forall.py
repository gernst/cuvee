from help_methods import requires, ensures, forall, imp


def nested_forall(a, x, y):
    requires(type(a) == list)
    requires(type(x) == int)
    requires(type(y) == int)
    requires(0 <= x and x < y and y < len(a))
    requires(forall(a, lambda y: type(a[y]) == int))
    requires(forall(a, lambda x, y: imp(x < y, a[x] <= a[y])))
    ensures(a[y] >= a[x])
