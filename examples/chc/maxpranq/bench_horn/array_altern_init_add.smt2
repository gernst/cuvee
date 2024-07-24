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
  (not (forall ((i1 Int))
    (=> (and (> i1 0) (< i1 n)) (exists ((j1 Int))
      (and (< j1 i1) (< (select a j1) (select a i1)))))))) fail))

(query fail)
