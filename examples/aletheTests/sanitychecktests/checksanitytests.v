(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.9, replace it with:
     Require Import SMTCoq.
   *)

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.
Require Import Int31.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Import FArray.
Local Open Scope farray_scope.

(* Examples that check ZChaff certificates *)

(*Local Open Scope int63_scope.*)
Local Open Scope int31_scope.
Local Open Scope array_scope.

Section Test1VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1.veritpf".
End Test1VeriT.

Section Test2VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test2.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test2.veritpf".
End Test2VeriT.

Section Test3VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test3.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test3.veritpf".
End Test3VeriT.

Section Test4VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test4.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test4.veritpf".
End Test4VeriT.

Section Test5VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test5.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test5.veritpf".
End Test5VeriT.

Section Test6VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test6.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test6.veritpf".
End Test6VeriT.

Section Test7VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test7.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test7.veritpf".
End Test7VeriT.

Section Test8VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test8.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test8.veritpf".
End Test8VeriT.

Section Test9VeriT.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test9.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test9.veritpf".
End Test9VeriT.

Section Test1cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1.cvc5pf".
End Test1cvc5.

Section Test2cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test2.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test2.cvc5pf".
End Test2cvc5.

Section Test3cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test3.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test3.cvc5pf".
End Test3cvc5.

Section Test4cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test4.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test4.cvc5pf".
End Test4cvc5.

Section Test5cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test5.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test5.cvc5pf".
End Test5cvc5.

Section Test6cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test6.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test6.cvc5pf".
End Test6cvc5.

Section Test7cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test7.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test7.cvc5pf".
End Test7cvc5.

Section Test8cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test8.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test8.cvc5pf".
End Test8cvc5.

Section Test9cvc5.
     Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test9.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test9.cvc5pf".
End Test9cvc5.