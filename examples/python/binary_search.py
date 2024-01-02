from help_methods import requires, ensures, forall, termination, old, imp, assume


def binary_search(a, x):
    requires(type(a) == list)
    requires(type(x) == int)
    requires(forall(a, lambda y: type(a[y]) == int))
    requires(forall(a, lambda x, y: imp(x <= y, a[x] <= a[y])))
    # requires(forall(a, lambda x,y: imp(x >= y, a[x] >= a[y])))
    # ensures(out() == (x in a))

    lo = 0
    hi = len(a) - 1
    mid = 0
    res = False
    while lo <= hi:
        requires(type(lo) == int)
        requires(type(hi) == int)
        requires(type(mid) == int)
        requires(type(res) == bool)
        requires(0 <= lo)
        requires(lo <= hi + 1)
        requires(hi <= len(a))
        requires(res == False)
        ensures(res == (x in a[old(lo):old(hi)+1]))
        termination(hi + 1 - lo)
        mid = lo + (hi - lo)//2
        if x == a[mid]:
            res = True
            assume(False)
            break
        elif x > a[mid]:
            lo = mid + 1
            assume(False)
        else:
            hi = mid - 1
            assume(False)
    assume(False)
    return res
