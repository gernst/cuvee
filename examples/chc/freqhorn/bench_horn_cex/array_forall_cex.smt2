(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var N Int)

(declare-rel inv1 ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (forall ((i Int)) (= (select a i) i)) (inv1 a 0 N)))

(rule (=> (and (inv1 a i N) (< i N)
  (= (store a i (- (select a i) (select a (+ i N)))) a1)
  (= i1 (+ i 1))) (inv1 a1 i1 N)))

(rule (=> (and (inv1 a i N) (>= i N) (< 0 i1) (< i1 N) (not (= (select a i1) 0))) fail))

(query fail)
