(set-option :print-success true)
(set-option :produce-assignments true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-option :sygus-core-connective false)
(set-logic QF_UF)
(declare-sort Tindex_1 0)
(declare-sort Tindex_0 0)
(declare-fun op_0 () Tindex_0)
(declare-fun op_3 () Tindex_0)
(declare-fun op_2 (Tindex_1 Tindex_0 ) Tindex_0)
(declare-fun op_4 (Tindex_0 Tindex_0 ) Tindex_0)
(declare-fun op_1 (Tindex_0 ) Tindex_1)
(get-abduct A (= (op_4 (op_2 (op_1 op_0) op_0) op_3) (op_4 op_0 op_3)))
;(define-fun A () Bool (= (op_2 (op_1 op_0) op_0) op_0))
