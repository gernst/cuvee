(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)

(declare-rel inv ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) 0) 0 n))

(rule (=> (and (inv a i n) (< i n)
  (= a1 (store a i (+ (select a i) i)))
  (= i1 (+ i 1))) (inv a1 i1 n)))

(rule (=> (and (inv a i n) (not (< i n))
    (>= i1 0) (< i1 n) (not (= (select a i1) i1))) fail))

(query fail)
