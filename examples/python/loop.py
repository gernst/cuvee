from help_methods import requires, ensures, termination


def loop(n):
    requires(n >= 0)
    requires(type(n) == int)
    # ensures(out() == n)
    i = 0
    while (i < n):
        requires(type(i) == int)
        requires(i <= n)
        ensures(i == n)
        termination(n - i)
        i = i + 1
    return i
