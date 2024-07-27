(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j1 Int)
(declare-var N Int)

(declare-rel inv ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (and (<= 0 i) (< i N) (< 0 N)) (inv ((as const (Array Int Int)) 0) 0 N)))

(rule (=> (and (inv a i N) (< i N)
    (= (store a i (+ 1 (select a i))) a1)
    (= i1 (+ i 1)))
  (inv a1 i1 N)))

(rule (=> (and (inv a i N) (>= i N)
  (not (exists ((j1 Int))
    (and (<= 0 j1) (< j1 N) (= (select a j1) 1))))) fail))

(query fail)
