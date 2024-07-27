(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var c (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)
(declare-var k Int)
(declare-var m Int)

(declare-rel inv ((Array Int Int) (Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (and (> k 0) (> m 0))
    (inv a ((as const (Array Int Int)) k)
           ((as const (Array Int Int)) m) 0 n)))

(rule (=> (and (inv a b c i n) (< i n)
  (= a1 (store a i (+ (select b i) (select c i))))
  (= i1 (+ i 1))) (inv a1 b c i1 n)))

(rule (=> (and (inv a b c i n) (not (< i n))
    (>= i1 0) (< i1 n) (not (> (select a i1) 0))) fail))

(query fail)
