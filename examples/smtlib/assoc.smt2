(set-logic ALL)

(declare-datatypes ((lst 0) (nat 0)) (((nil) (cons (cons0 nat) (cons1 lst))) ((zero) (s (s0 nat)))))
(declare-fun app (lst lst) lst)

; (assert (forall ((x lst) (y lst) (z lst))   (= (app (app x y) z)       (app x (app y z)))))

(assert (forall ((r lst)) (= (app nil r) r)))
(assert (forall ((a nat) (l lst) (r lst)) (= (app (cons a l) r) (cons a (app l r)))))

(assert (not (forall ((v0 lst)) (= (app (app (app v0 v0) (app v0 (app v0 v0))) (app (app (app v0 v0) v0) v0)) (app (app (app v0 (app v0 (app v0 v0))) v0) (app (app v0 v0) (app v0 v0)))))))
(check-sat)