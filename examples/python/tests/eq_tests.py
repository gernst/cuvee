from cuvee import out, ensures, requires, imp


def eq(a, b):
    requires(type(a) == int)
    requires(type(a) == type(b))
    ensures(out() == (a == b))
    a = b
    return a == b


def not_eq(a, b):
    requires(type(a) == type(b))
    ensures(out() == (a != b))
    return a != b


def eq_div(a, b):
    ensures(out() == (a == b))
    return a == b


def lt(a, b):
    requires(type(a) == type(b))
    requires(a < b)
    ensures(out())
    if a < b:
        return True
    else:
        return False


def leq(a, b):
    requires(type(a) == type(b))
    ensures(out() == (a <= b))
    return a <= b


def leq_div(a, b):
    ensures(imp(a <= b, out() == a))
    if a <= b:
        return a
    else:
        return b


def gt(a, b):
    requires(type(a) == type(b))
    ensures(imp(a >= b, out() == 7))
    if a >= b:
        return 7


def geq(a, b):
    requires(type(a) == type(b))
    ensures(imp(a <= b, out()))
    b = a
    if a <= b:
        return True
    else:
        return False


def fail_eq(a, b):
    requires(type(a) == type(b))
    ensures(a == b)
    return a == b


def fail_leq_div(a, b):
    requires(a == b)
    ensures(a <= b)
