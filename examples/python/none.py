from help_methods import ensures, out


def none_():
    ensures(out())

    assert None == None

    if (None):
        return False
    else:
        return True
