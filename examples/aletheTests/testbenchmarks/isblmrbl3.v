Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/testbenchmarks/isblmrbl3.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/testbenchmarks/isblmrbl3.pf".
End Benchmark.
(*
This one fails because of the following congruence:
(t2, ItesimpAST, (cl  (((ite  p_d (true) q_d) = (or  p_d q_d)))), [], [])
(t3, CongAST, (cl  ((((ite  p_d (true) q_d) = (or  p_d q_d)) = ((or  p_d q_d) = (or  p_d q_d))))), [ t2], [])
`t3` performs a `cong` over the `iff` function, which we haven't implemented yet.
*)