(set-logic QF_BV)
(assert (= (bvnot #b0) #b0))
(check-sat)
(exit)
