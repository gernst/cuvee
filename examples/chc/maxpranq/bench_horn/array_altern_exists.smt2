(declare-var a (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)
(declare-var x Int)

(declare-rel inv ((Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (=> (exists ((j1 Int)) (and (<= 0 j1) (< j1 n) (= (select a j1) x))) (inv a 0 x n)))

(rule (=> (and (inv a i x n) (< i n) (not (= (select a i) x)) (= i1 (+ i 1))) (inv a i1 x n)))

(rule (=> (and (inv a i x n) (or (not (< i n)) (= (select a i) x)) (not (< i n))) fail))

(query fail)
