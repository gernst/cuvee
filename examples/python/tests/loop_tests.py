from cuvee import out, ensures, requires, decreases


def loop(n):
    requires(n >= 0)
    requires(type(n) == int)
    # ensures(out() == n)
    i = 0
    while (i < n):
        requires(type(i) == int)
        requires(i <= n)
        ensures(i == n)
        ensures(out() == n)
        decreases(n - i)
        i = i + 1
    return i
