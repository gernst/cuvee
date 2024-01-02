from help_methods import requires, ensures, out, termination


def linear_search(a, x):
    requires(type(a) == list)
    ensures(out() == (x in a))
    i = 0
    res = False
    while i < len(a):
        requires(type(i) == int)
        requires(0 <= i and i <= len(a))
        requires(res == (x in a[:i]))
        ensures(res == (x in a))
        termination(len(a) - i)
        if a[i] == x:
            res = True
        i = i + 1
    return res
