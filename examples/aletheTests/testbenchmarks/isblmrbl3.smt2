; --proof-with-sharing --index-fresh-sorts --proof-define-skolems --proof-prune --proof-merge --disable-print-success --disable-banner --max-time=30
(set-option :produce-proofs true)
(set-logic AUFLIA)
(declare-fun p_d () Bool)
(declare-fun q_d () Bool)
(assert (! (not (= (ite p_d true q_d) (or p_d q_d))) :named a0))
(check-sat)
;;;;;;(get-proof)
