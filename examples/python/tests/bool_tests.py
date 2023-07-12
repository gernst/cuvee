from help_methods import out, ensures, requires, imp


def assign_bool(a, b):
    ensures(out() == a)
    a = True
    b = False
    return a


def impl(a):
    requires(type(a) == bool)
    ensures(imp(a, out() == False))
    if a:
        return False


def land(a, b, c):
    requires(a and b and c)
    ensures(d)
    d = (a and b and c)


def lor(a, b, c):
    requires(a)
    ensures(d and a or c)
    d = a or b or c


def lnot(a):
    requires(type(a) == bool)
    requires(a)
    ensures(not b)
    b = not a


def ite(a):
    requires(type(a) == bool)
    ensures((a and b) or not (a or c))
    if a:
        b = a
        c = b
    else:
        c = a
        b = c


def fail_lor(a, b, c):
    requires(a)
    ensures(d and a and c)
    d = a or b or c


def fail_impl(a):
    requires(type(a) == bool)
    ensures(imp(a, out() == True))
    if not a:
        return True


def fail_ite(a):
    requires(type(a) == bool)
    ensures(a and b or a or c)
    if a:
        b = a
        c = b
    else:
        c = a
        b = c
