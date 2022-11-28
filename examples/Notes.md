We have 7 sanity check tests:
| Test | Goal | Success | # Steps Before AST | # Steps After AST | Comments |
|------|------|---------|--------------------|-------------------|----------|
|ex1   |$\neg (\top \land \neg \top)$|Fail|1 + 9|1 + 37||
|ex2   |$\top \lor \bot$|Fail|1+12|1+46||
|ex3   |$\forall p,\ \neg (p \land \neg p)$|Fail|1+5|1+14||
|ex4   |$\forall a\ b\ c,\ ((a \lor b \lor c) \land (\neg a \lor \neg b \lor \neg c) \land (\neg a \lor b) \land (\neg b \lor c) \land (\neg c \lor a)) = false$| Success|1+14|1+14| No simplify rules|
|ex5   |$\forall p,\ p \lor \neg p$|Fail|1+10|1+30||
|ex6   |$\forall (a\ b : \mathbb{Z})\ (P : \mathbb{Z} -> Bool)\ (f : \mathbb{Z} -> \mathbb{Z}),\ (f\ a \neq b) \lor (\neg P (f\ a)) \lor (P\ b)$|Success|1+9|1+7|No simplify rules|
|ex7   |$(\forall (x : \mathbb{Z}),\ P\ x) -> P\ a$|Success|1+16|1+4|No simplify rules|

Tests 4, 6, 7 pass. Tests 1, 2, 3, 5 fail with the message `SMTCoq was not able to check the proof certificate`. The difference between these is that there are no `simp` rules in the ones that pass. So we don't have any proofs that work with simp rules in them.
Next steps:
1. 3 is the smallest of the certificates that fails, do step-by-step debugging on it.
2. Once all the sanity check tests pass with process_simplify, we want to try out `sledgehammerTests.v` which consists of a much bigger suite.
3. Finally, we need to run `cvc5` on the same set of tests and maybe take stock of the `all_simplify` rules, and use the DSL to rewrite these in terms of the alethe `_simplify` rules.