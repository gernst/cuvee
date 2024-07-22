(declare-var a (Array Int Int))
(declare-var a0 (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)
(declare-var c Int)
(declare-rel inv0 ((Array Int Int) Int Int Int))
(declare-rel inv1 ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv0 a 0 75 n))

(rule (=> (and (inv0 a i c n) (< i n)
  (= a0 (ite (< i 3) (store a i c) (store a i (select a (- i 3)))))
  (= i1 (+ i 1))) (inv0 a0 i1 c n)))

(rule (=> (and (inv0 a0 i c n) (not (< i n))) (inv1 a0 a 0 c n)))

(rule (=> (and (inv1 a a0 i c n) (< i n)
  (= a1 (store a0 i c))
  (= i1 (+ i 1))) (inv1 a a1 i1 c n)))

(rule (=> (and (inv1 a0 a1 i c n) (not (< i n))
  (<= 0 i1) (< i1 n) (not (= (select a0 i1) (select a1 i1)))) fail))

(query fail)
