(declare-var a (Array Int Int))
(declare-var v Int)
(declare-var N Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var a1 (Array Int Int))
(declare-var n Int)

(declare-rel inv ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (and (<= 0 n) (< n N)) (inv ((as const (Array Int Int)) n) 0 N)))

(rule (=> (and
           (inv a i N)
           (< i N)
           (= a1 (store a i (* 2 (select a i))))
           (= i1 (+ i 1)))
          (inv a1 i1 N)))

(rule (=> (and (inv a i N)
    (>= i N)
    (not (exists ((j Int)) (and (<= 0 j) (< j N) (= (select a j) (* 2 j))))))
  fail))

(query fail)
