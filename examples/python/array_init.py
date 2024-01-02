from help_methods import requires, ensures, out, forall, termination, old


def array_init(a):
    requires(type(a) == list)
    ensures(forall(out(), lambda x: out()[x] == 0))
    i = 0
    while (i < len(a)):
        requires(type(i) == int)
        requires(type(a) == list)
        requires(0 <= i and i <= len(a))
        requires(len(a) == old(len(a)))
        requires(forall(a[0:i], lambda x: a[x] == 0))
        ensures(forall(a, lambda x: a[x] == 0))
        termination(len(a) - i)
        a[i] = 0
        i = i + 1
    return a
