from cuvee import out, ensures, requires, imp


def abs(x):
    requires(type(x) == int)
    ensures(out() >= 0)
    if (x < 0):
        return -x
    else:
        return x


def abs_fail(x):
    requires(type(x) != list)
    ensures(out() >= 0)
    if (x < 0):
        return -x
    else:
        return x

# def abs_general(x): # TODO
#     requires(type(x) == int or type(x) == bool)
#     ensures(imp(type(x) == int, out() >= 0))
#     ensures(imp(type(x) == bool, out() != 0))
#     if type(x) == int:
#         if (x < 0):
#             return -x
#         else:
#             return x
#     else:
#         if x:
#             return 1
#         else:
#             return -1


def add(x, y):
    requires(type(x) == type(y))
    ensures(out() == x + y)
    return x + y


def sub(x, y):
    requires(type(x) == type(y) and not type(x) == list)
    ensures(out() == (x - y))
    return x - y


def mult(x, y):
    requires(type(y) != list)
    ensures(out() == (x * y))
    return x * y


def div(x, y):
    requires((type(x) == int and type(y) == int and y != 0)
             or (type(x) == int and type(y) == bool and y != False))
    ensures(out() == (x // y))
    return x // y


def mod(x, y):
    requires((type(x) == int and type(y) == int and y > 0)
             or (type(x) == int and type(y) == bool and y != False))
    ensures(out() < y)
    return x % y
