(set-logic UFLIA)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (= a x))
(assert (= b y))
(assert (not (= (= a b) (= x y))))
(check-sat)
(exit)
