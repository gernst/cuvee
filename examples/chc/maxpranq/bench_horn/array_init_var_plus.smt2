(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var N Int)

(declare-rel inv ((Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (=> (and (= i 0) (= j 0)) (inv a i j N)))

(rule (=> (and (inv a i j N) (< i N) (= (store a i j) a1) (= j1 (+ j i)) (= i1 (+ i 1))) (inv a1 i1 j1 N)))

(rule (=> (and (inv a i j N) (not (< i N)) (< 0 i1) (< i1 i) (not (>= (select a i1) 0))) fail))

(query fail)
