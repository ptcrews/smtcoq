# Dev Notes on Adding a Tactic
Using the experience of adding the `abduce` tactic, this document summarizes the process of adding a tactic to SMTCoq.

## Tactic Logic
The logic of the tactic is implemented in OCaml, in this case in the [Lfsc module](../src/lfsc/lfsc.ml). The 
`abduce` tactic takes an integer `n` as an argument. It calls `cvc4` on the current goal (also collecting all the 
hypotheses and asserting them) and if it finds it to be satisfiable, it calls `cvc5`, asking it to find `n` abducts
that it presents to the user.

The `call_cvc4_abduct` function collects and asserts the hypotheses and the negation of the goal. If it finds this 
combination to be unsatisfiable, it asks the Coq user to call the `smt` tactic instead. If it finds it to be satisfiable,
it calls the `call_abduce` function, which calls the abduction solver from `cvc5` using the following utilities. 
`call_cvc4_abduct` is exposed from the `Lfsc` module via the `tactic_abduct` function.

## Queries to the SMT Solver
`call_abduce` opens `cvc5` in interactive mode where each command is called and its result processed. Commands to the SMT solver 
are sent through [Smtlib2_solver](../src/smtlib2/smtlib2_solver.ml): `get_abduct` and `get_abduct_next` are used for the 
abduction queries.

## SMT Solver Response
[SmtCommands](../src/trace/smtCommands.ml) contains functions to parse responses from the SMT solver. `abduct_string` is used to 
parse the abducts into S-expressions which are then converted to strings and printed by `call_abduce`.

## Additional Argument `n`
As mentioned above, the `abduce` tactic takes an integer argument `n` specifiying the number of abducts to get. Since all of SMTCoq's
tactics involve calls to the SMT solver, they all have some common code in [SmtCommands](../src/trace/smtCommands.ml) which 
includes the functions `make_proof`, `core_tactic`, and `tactic`. This integer argument is passed on from `call_cvc4_abduct` to
`call_abduce` all the way down to these 3 functions where changes need to be made (the argument must be added to all of them and
a default value must be specified when it doesn't apply). This must also be done with the other tactic logic functions in 
[Lfsc](../src/lfsc/lfsc.ml) and [Verit](../src/verit/verit.ml).

## Front-end
Finally, the tactic can be exposed to Coq. First, in [g_smtcoq.mlg](../src/g_smtcoq.mlg), `cvc5_bool_abduct` is specified as 
an extension of the `Tactic_cvc4` group of tactics, which simply calls `tactic_abduct` from [Lfsc](../src/lfsc/lfsc.ml).
Then, in the Coq file [Tactics](../src/Tactics.v), `abduce` is defined as a `Tactic Notation` and Ltac code is used to 
collect the hypotheses, the goal, the value of `n`, and they are passed on to `call_cvc4_abduct` through `cvc5_bool_abduct`.