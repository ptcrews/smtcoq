(set-logic UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ a 1) (* 2 b)))
(assert (not (= (= (+ a 1) y) (= (* 2 b) y))))
(check-sat)
(exit)
