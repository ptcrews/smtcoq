(set-logic UFLIA)
(declare-fun x () Bool)
(assert (not (not x)))
(assert (not x))
(check-sat)
(exit)
