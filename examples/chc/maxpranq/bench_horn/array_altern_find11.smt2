(declare-var a (Array Int Int))
(declare-var v Int)
(declare-var N Int)
(declare-var i Int)
(declare-var r Int)
(declare-var i1 Int)
(declare-var r1 Int)

(declare-rel inv ((Array Int Int) Int Int Int Int))
(declare-rel fail ())

(rule (inv a 0 N v N))

(rule (=> (and (inv a i r v N)
    (< i N)
    (= r N)
    (= r1 (ite (= (select a i) v) i r))
    (= i1 (+ i 1)))
  (inv a i1 r1 v N)))

(rule (=> (and (inv a i r v N)
    (not (and (< i N) (= r N)))
    (not (=> (and (<= 0 N) (not (= r N)))
             (exists ((pos Int)) (= (select a pos) v)))))
  fail))

(query fail)
