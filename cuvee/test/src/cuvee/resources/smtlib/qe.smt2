(declare-const y Int)
(assert (exists ((x Int)) (and (> x 0) (<= x y))))
(assert (< (- 25) y))
(check-sat)