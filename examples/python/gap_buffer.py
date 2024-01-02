from help_methods import requires, ensures, old


class GapBuffer:
    def __init__(self):
        self.a = []
        self.l = 0
        self.r = 0

    def left(self):
        requires(type(self.a) == list and type(
            self.l) == int and type(self.r) == int)
        requires(self.l > 0 and self.l <= self.r and self.r <= len(self.a))
        ensures(self.r == old(self.r) - 1)
        ensures(self.l == old(self.l) - 1)
        ensures(self.a[:self.l] + self.a[self.r:] ==
                old(self.a[:self.l] + self.a[self.r:]))

        self.l = self.l - 1
        self.r = self.r - 1
        self.a[self.r] = self.a[self.l]

    def right(self):
        requires(type(self.a) == list and type(
            self.l) == int and type(self.r) == int)
        requires(self.l >= 0 and self.l <= self.r and self.r < len(self.a))
        ensures(self.l == old(self.l) + 1)
        ensures(self.r == old(self.r) + 1)
        ensures(self.a[:self.l] + self.a[self.r:] ==
                old(self.a[:self.l] + self.a[self.r:]))

        self.a[self.l] = self.a[self.r]
        self.l = self.l + 1
        self.r = self.r + 1

    def insert(self, x):
        requires(type(self.a) == list and type(
            self.l) == int and type(self.r) == int)
        requires(type(x) == int)
        requires(self.l >= 0 and self.l <= self.r and self.r < len(self.a))
        ensures(self.a[old(self.l)] == x)
        ensures(self.l == old(self.l) + 1)
        ensures(self.a[:self.l] + self.a[self.r:] ==
                old(self.a[:self.l]) + [x] + old(self.a[self.r:]))

        if self.l == self.r:
            self.grow()
        self.a[self.l] = x
        self.l = self.l + 1

    def delete(self):
        requires(type(self.a) == list and type(
            self.l) == int and type(self.r) == int)
        requires(self.l > 0)
        ensures(self.l == old(self.l) - 1)
        ensures(self.a[:self.l] + self.a[self.r:] ==
                old(self.a[:self.l-1] + self.a[self.r:]))

        self.l = self.l - 1

    def grow(self):
        requires(type(self.a) == list and type(
            self.l) == int and type(self.r) == int)
        requires(self.l >= 0 and self.l == self.r and self.r < len(self.a))

        self.a = self.a[:self.l] + [0, 0, 0] + self.a[self.r:]
        self.r = self.r + 3
