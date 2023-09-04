from cuvee import out, ensures, requires, decreases


def loop(n):
    requires(n >= 0)
    requires(type(n) == int)
    ensures(out() == n)
    i = 0
    while (i < n):
        invariant(type(i) == int)
        invariant(i <= n)
        decreases(n - i)
        i = i + 1
    return i
