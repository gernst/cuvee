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
(declare-var N1 Int)
(declare-var M Int)
(declare-var M1 Int)

(declare-rel pre (Int Int (Array Int Int) (Array Int Int) (Array Int Int) Int))
(declare-rel inv (Int Int (Array Int Int) (Array Int Int) (Array Int Int) Int))
(declare-rel fail ())

(rule (=> (and (pre i N a b c M) (> N 0) (= N1 N) (= i 0)) (inv i N1 a b c M)))

(rule (=> (and (inv i N a b c M) (< i N) (< i M) (= (store c i i) c1) (= (store b i (select b i)) b1) (= (store a i (select a i)) a1) (= i1 (+ i 1))) (inv i1 N a1 b1 c1 M)))

(rule (=> (and (inv i N a b c M) (< i N) (>= i M) (= (store a i (select c i)) a1) (= (store b i (select b i)) b1) (= (store c i (select c i)) c1)(= i1 (+ i 1))) (inv i1 N a1 b1 c1 M)))


(rule (=> (and (inv i N a b c M) (>= i N) (<= 0 i1) (< i1 N) (not (= (select a i1) (select b i1)))) fail))

(query fail)
