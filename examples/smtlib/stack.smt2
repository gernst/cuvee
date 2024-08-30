(declare-const x Int)
(declare-const y Int)

(push)
(assert (= x 1))
(assert (= y 2))
(assert (distinct (+ x y) 3))
(check-sat)
(pop)

(assert false)
(check-sat)