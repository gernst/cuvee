(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv a ((as const (Array Int Int)) 0) 0 n))

(rule (=> (and (inv a b i n) (< i n)
  (= a1 (store a i (+ (select b i) i)))
  (= i1 (+ i 1))) (inv a1 b i1 n)))

(rule (=> (and (inv a b i n) (not (< i n))
    (>= i1 0) (< i1 n) (not (>= (select a i1) 0))) fail))

(query fail)
