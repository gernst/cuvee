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

(declare-rel pre (Int (Array Int Int) (Array Int Int) (Array Int Int)))
(declare-rel inv (Int Int (Array Int Int) (Array Int Int) (Array Int Int)))
(declare-rel fail ())

(rule (=> (and (pre N a b c) (= i 0)) (inv i N a b c)))

(rule (=> (and (inv i N a b c) (< i N) (= (store a i (select c i)) a1) (= (store b i (select b i)) b1) (= (store c i (select c i)) c1) (= i1 (+ i 1))) (inv i1 N a1 b1 c1)))

(rule (=> (and (inv i N a b c) (< i N) (= (store a i (+ (select c i) (select b i))) a1) (= (store b i (select b i)) b1) (= (store c i (select c i)) c1)(= i1 (+ i 1))) (inv i1 N a1 b1 c1)))

(rule (=> (and (inv i N a b c) (>= i N) (<= 0 i1) (< i1 N) (not (= (select a i1) (select c i1)))) fail))

(query fail)
