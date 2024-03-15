(set-logic QF_BV)
(assert (= (bvand #b0 #b0) #b1))
(check-sat)
(exit)
