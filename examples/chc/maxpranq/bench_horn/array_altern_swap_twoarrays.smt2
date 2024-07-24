(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var n Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (forall ((j1 Int)) (=> (and (>= j1 0) (< j1 n))
  (exists ((i2 Int)) (= (select a j1) (select b i1))))) (inv a b 0 n)))

(rule (=> (and (inv a b i n)
  (< i n)
  (= i1 (+ i 1))
  (= a1 (store a i (select b i)))
  (= b1 (store b i (select a i))))
    (inv a1 b1 i1 n)))

(rule (=> (and (inv a b i n) (not (< i n))
  (not (forall ((j1 Int)) (=> (and (>= j1 0) (< j1 n))
    (exists ((i2 Int)) (= (select a i2) (select b j1))))))) fail))

(query fail)
