(set-option :print-success true)
(set-option :produce-assignments true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic QF_UF)
(declare-sort Tindex_0 0)
(declare-sort Tindex_1 0)
(declare-sort Tindex_2 0)
(declare-sort Tindex_3 0)
(declare-sort Tindex_4 0)
(declare-fun op_4 (Tindex_4 Tindex_2 ) Tindex_3)
(declare-fun op_1 () Tindex_2)
(declare-fun op_6 (Tindex_3 ) Tindex_0)
(declare-fun op_9 (Tindex_0 Tindex_0 ) Tindex_0)
(declare-fun op_3 () Tindex_4)
(declare-fun op_8 (Tindex_4 ) Tindex_0)
(declare-fun op_7 (Tindex_2 ) Tindex_0)
(declare-fun op_10 (Tindex_0 Tindex_0 ) Tindex_0)
(declare-fun op_2 (Tindex_1 Tindex_2 ) Tindex_3)
(declare-fun op_0 () Tindex_1)
(declare-fun op_5 (Tindex_3 Tindex_3 ) Tindex_3)
(get-abduct A (= (op_6 (op_5 (op_2 op_0 op_1) (op_4 op_3 op_1))) (op_10 (op_7 op_1) (op_9 (op_8 op_3) (op_7 op_1)))))

