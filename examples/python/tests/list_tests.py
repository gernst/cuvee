from help_methods import out, ensures, requires, imp, old, forall, exists


def elem_0(a):
    requires(type(a) == list)
    ensures(out()[0] == 0)
    a = [0]
    return a


def forall_elem_0(a):
    requires(type(a) == list)
    requires(len(a) == 1)
    ensures(forall(out(), lambda x: out()[x] == 0))
    a = [0]
    return a


def old_list(a):
    requires(type(a) == list)
    requires(out() == old(a))
    return a


def switch_elem(a):
    requires(type(a) == list)
    requires(len(a) >= 2)
    ensures(out()[0] == a[1] and out()[1] == a[0])
    ensures(forall(out(), lambda x: imp(1 < x, out()[x] == a[x])))
    tmp = a[1]
    a[1] = a[0]
    a[0] = tmp
    return a


def slice_r(a):
    requires(type(a) == list)
    requires(len(a) > 3)
    ensures(exists(out(), lambda x: out()[x] == 0))  # suggestion
    # ensures(0 in out())  # The problem is apparently this predicate
    a[1] = 0
    return a[:2]


def slice_l_r(a):
    requires(type(a) == list)
    requires(len(a) > 3)
    ensures(out()[0] == 0)
    a[1] = 0
    return a[1:2]


def copy(a, b):
    requires(type(a) == list and type(b) == list)
    ensures(forall(out(), lambda x: imp(
        0 <= x and x < len(b), out()[x] == b[x])))
    a = b[:]
    return a
