from help_methods import requires, ensures, old


class Counter:
    def __init__(self):
        self.counter = 0

    def incr(self):
        requires(type(self.counter) == int)
        ensures(self.counter == old(self.counter) + 1)
        self.counter = self.counter + 1

    def get_count(self):
        return self.counter
