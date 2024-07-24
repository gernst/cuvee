(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var c (Array Int Int))
(declare-var c1 (Array Int Int))
(declare-var i Int)
(declare-var j Int)
(declare-var i1 Int)
(declare-var N Int)
(declare-var m1 Int)
(declare-var m2 Int)

(declare-rel pre (Int Int Int (Array Int Int) (Array Int Int) (Array Int Int)))
(declare-rel inv (Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int)))
(declare-rel fail ())

(rule (=> (and (pre N m1 m2 a b c) (= i 0)) (inv i N m1 m2 a b c)))

(rule (=> (and (inv i N m1 m2 a b c) (< i N) (= (store a i (- (select c i) m1)) a1) (= (store b i (select b i)) b1) (= (store c i (select c i)) c1) (= i1 (+ i 1))) (inv i1 N m1 m2 a1 b1 c1)))

(rule (=> (and (inv i N m1 m2 a b c) (< i N) (= (store a i (- (select b i) m2)) a1) (= (store b i (select b i)) b1) (= (store c i (select c i)) c1)(= i1 (+ i 1))) (inv i1 N m1 m2 a1 b1 c1)))

(rule (=> (and (inv i N m1 m2 a b c) (>= i N) (<= 0 i1) (< i1 N) (not (>= (select a i1) 0))) fail))

(query fail)
