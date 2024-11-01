(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)

(declare-rel inv ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) 0) 0 n))

(rule (=> (and (inv a i n) (< i (* 2 n))
  (= a1 (ite (= (mod i 2) 1) (store a i 1) a))
  (= i1 (+ i 1))) (inv a1 i1 n)))

(rule (=> (and (inv a i n) (not (< i (* 2 n)))
  (not (forall ((i1 Int))
    (=> (and (>= i1 0) (< i1 (* 2 n)) (= (select a i1) 0)) (exists ((j1 Int))
      (and (> j1 i1) (= (select a j1) 1))))))) fail))

(query fail)
