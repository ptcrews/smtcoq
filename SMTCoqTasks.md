SMTCoq currently parses veriT 2016's proof format, and builds OCaml AST's that it reify's to Coq AST's checked by the Coq checker. It also translates LFSC proofs from CVC4 to these same OCaml AST's. VeriT now uses a proof format called Alethe which will be supported by CVC5 also. We want to upgrade SMTCoq's veriT parser so that it can parse Alethe proofs, as a consequence of which, the LFSC parser and translator can be removed as well. This will entail the following tasks:
- [x] Update the Ocamlyacc parser to a Menhir parser
- [x] Remove the LFSC parser and temporarily remove the `cvc4` tactic
- [x] Update the parser to parse Alethe instead of veriT 2016 proofs. Remove rules that Alethe doesn't support
- [x] Currently, we're assuming an ordering on the step numbers - we assume they are `t1,...,tn` and we don't account for sub-proofs, which would be `ti.tj`. Eventually update this to take any series of step numbers and convert them internally to an order we care about
- [x] Support cvc4 v1.8
- [x] Add an AST layer so we go parser -> AST -> AST transformations -> SMTCoq terms
	- [x] Add better error handling so we can figure out which line has an error.
- [x] Separate all Alethe rules into categories, and mark the rules which are already implemented.
- [x] Add better error handling so we can figure out which line has an error.
- [ ] Add Propositional logic + EUF rules
	- [x] `trans` rule, `cong` rule predicate case
	- [x] Process cong rule by adding two steps
	- [x] Simplification rules: `not_simplify`, `and_simplify`, `or_simplify`, `implies_simplify`, `equiv_simplify`, `ite_simplify`, `connective_def`, `bool_simplify`, `eq_simplify`
		- [x] Fix `and_simplify` and `or_simplify` rules by fixing parsing of variables
	- [x] `not_not` , `tautology`, `contraction` rules
	- [x] Rules `and_pos`, `or_neg`, `and`, `not_or` all had arguments in the previous format, but Alethe makes the arguments implicit. Change the parser so it finds the arguments
	- [x] Rule `eq_congruent_pred` had 2 separate literals for the equality of the conclusion in the previous format, Alethe combines them in a single `iff` literal, change the checker
		- [x] Turns out Alethe spec was incorrect and they didn't mean to 
		make this change to the rule. Change the checker back 
	- [x] `th_resolution` is exactly the same as `resolution` (according to the spec), but it doesn't seem to work. 
		- [x] `th_resolution` chains the resolutions in an order of premises that is reverse of the order that `resolution` uses. Change the order of chaining in the checker.
	- [x] Add the function case for the `cong` rule by composing `resolution` and `eq_congruent`
	- [x] Fix the `not_not` rule.
		- [x] Parse double negations into `Fnot2` and not two negations. This still doesn't work, since many rules eliminate double negations, so once the clauses produced by
		these rules are resolved with one produced by `not_not`, we have a mismatch of the pivot (`Form.neg (Fnot2 1 x)` vs `x`, instead of `Fnot2 1 x`).
		- [x] Change `not_not` from `~~x -> x` to `x -> x` and then eliminate double negations while parsing. This maintains consistency in the logic so that `not_not` clauses
		can be resolved with others. However, in resolution, when the clauses being resolved have a common literal, that literal is taken out of consideration for being a pivot, and 
		this makes an invalid resolution.
		- [x] Take an Alethe proof with `not_not` and translate it into a proof without `not_not`.
	- [ ] `distinct_elim` rule, which is pretty similar to `SplDistinctElim`
		  Exception: `distinct` is a function over terms, and formulas in SMT, but in Coq it is only defined over terms
			- [ ] Implement the formula version of `distinct` in SMTCoq
			- [ ] Add the formula cases for `distinct_elim`
	- [ ] `refl` rule which does the same thing as `eq_reflexive` unless used modulo context substitutions. We handle the latter case that we care about (`bind` in `forall_inst`)
	- [ ] Simplification rules: `ac_simp`
		- [x] Define array append
		- [ ] BLOCKED: Need a way to re-hash unhashed formulas
		- [ ] Check if final order of clause is predictable
		- [ ] Check the rule checker in Bruno's Alethe checker
	- [ ] The simp rules are not recursively applied yet. Counterexamples show it isn't applied recursively by veriT. The goal is to have VeriT apply them recursively so change the checker when the implementation is fixed.
	- [ ] Find certificates to test the implementation of these rules: `tautology`, `contraction`, `implies_simplify`, `equiv_simplify`, `ite_simplify`, `connective_def`, `bool_simplify`, `connective_def`, `eq_simplify`, `and_pos`, `or_neg`, `not_or`, `eq_congruent_pred`
	- [ ] Correctness proofs
		- [ ] Many of the `_simplify` rules have admitted proofs. Either prove them correct or
			  encode them in terms of existing rules.
			- [ ] DistElim (src/spl/Operators.v)
			- [ ] NotNot (src/cnf/Cnf.v: remove the rule in the back-end since we're removing it at the AST level)
			- [ ] Tautology (src/cnf/Cnf.v)
				- [ ] change the checker - remem- [x] Add an AST to SMTCoq and parse SMT proofs into the AST format, and then define a function that translte the AST to `mk_clause` that was previously being done with the parser.
			- [ ] OrSimplify (src/cnf/Cnf.v)
			- [ ] ImpliesSimplify (src/cnf/Cnf.v)
			- [ ] EquivSimplify (src/cnf/Cnf.v)
			- [ ] BoolSimplify (src/cnf/Cnf.v)
			- [ ] ConnDef (src/cnf/Cnf.v)
			- [ ] IteSimplify (src/cnf/Cnf.v)
			- [ ] IffTrans (src/cnf/Euf.v)
			- [ ] IffCong (src/cnf/Euf.v)
			- [ ] EqSimplify (src/cnf/Euf.v)
- [x] Add Arithmetic rules
	- [x] Implement `lia_generic`, `la_tautology`, `la_disequality` as they were by the old parser
	- [x] Arith simplify rules: `div_simplify`, `prod_simplify`, `unary_minus_simplify`, `minus_simplify`
	- [x] `la_rw_eq` rule
	- [x] Modify parser for `la_generic` which now takes arguments
	- [x] Test
- [ ] Add Bit-vector rules
	- [x] How does a regular LFSC proof look vs a veriT proof?
	- [x] How does an LFSC BV proof look?
	- [x] Revisit the old LFSC proof signature- [x] Separate all Alethe rules into categories, and mark the rules which are already implemented.
	- [ ] Check out Haniel's Lean signature
	- [x] How does the LFSC to VeriT translator handle bit-vectors and arrays? Seemingly, the VeriT proof format was extended with BV
	and array rules and when LFSC proofs used rules in these theories,
	those rules were converted to applications of these extended rules.
	- [ ] Extend Alethe with BV proof rules
	- [ ] Add rules to SMTCoq
- [ ] Add Array rules
	- [ ] Extend Alethe with Array proof rules
	- [ ] Add rules to SMTCoq
- [ ] Add quantifier rules
	- [x] What support for quantifiers does SMTCoq currently have?
	- [x] Add parser for quantified terms
	- [x] Find the goal in SMTCoq that leads to the basic quantifers example, and check if its as expected.
	- [x] Currently VeriT is called with term sharing turned off, need to be able to deal with shared terms
	- [x] Run the example proof through the old SMTCoq to find examples of Chantal's explanation.
	- [x] Read the skolemization section in the book
	- [x] grep Sledgehammer benchmarks for `forall_inst` and see if new veriT changes instances so they are different from the quantified lemma or not.
	- [x] Make a feature request to the veriT group to remove alpha renaming of proofs with quantifiers. This request was denied because it is complicated to do from veriT's point of view.
	- [x] With the current Alethe proofs, parse subproofs and parse `bind` as a no-op and for all resolutions, remove the `bind` `equiv_pos2` premises. Do this via an AST transformation
	- [ ] Why is it more complicated in Coq to prove `(forall Q1.H1) -> ... -> (forall Qn.Hn) -> G` as opposed to 
	`forall Q1..Qn.H1 -> ... -> Hn -> G`?
		- [ ] Read quantifier subsection of logic section of Software foundations.
	- [ ] Read spec of all quantifier rules
	  - [x] bind: supported with forall_inst by ignoring
	  - [x] sko_ex: SMTCoq doesn't support existentials
	  - [x] forall_inst: we have a transformation for this
	  - [ ] sko_forall
	  - [ ] qnt_simplify
	  - [ ] onepoint
	  - [ ] qnt_join
	  - [ ] qnt_rm_unused
- [ ] Add support for subproofs using Chantal's flattening method. Do this via an AST transformation
	- [x] First approach wasn't general enough. This was embarrassingly discovered at a talk given to Deducteam at the end of my Paris trip.
	- [ ] Draw out the more general approach
	- [x] Create a hand-made example for more general approach.
	- [ ] Implement
	- [ ] Check with Haniel
- [ ] Set up testing of benchmarks
	- [x] Generate proofs for all benchmarks.
	- [x] Generate proofs with sharing for all benchmarks.
	- [x] Search tests to answer the following.
		- [x] How many proofs contain subproofs? How many are quantifier-free?
		- [x] How many proofs contain subproofs that are simply alpha-renamings?
	- [x] Generate `verit_proof_parser` vernac for generic proof file
		- [ ] Can we generalize this? We will need to use programming in Coq. 
		- [ ] Generate a coq file that checks each file in the Sledgehammer benchmarks
	  as follows. (Quantifier files might not work :( )
	  	```
	  	Section Filename.
  			Verit_Checker "Filename.smt2" "Filename.smt_inproofnew".
		End Filename.
		```
	- [ ] Run tests in smtcoq/unit-tests/Tests_verit_tactics.v


- [ ] Support abduction
	- [x] Create a `cvc5_abduct` tactic that will return 5 abducts if the solver returns `sat`
	- [x] Add an integer parameter to `cvc4_abduct` specifying the number of abducts
	- [x] Find the smallest example from benchmarks
	- [x] Create small examples that manually illustrate the usage of abduction
	- [x] Do we change the output of `cvc4_abduct` to an idtac when sat? No, right now its an error, and that makes sense, because an idtac would add it to the proof development, and the solver would be called everytime the proof is compiled, which would be unnecessary.
	- [ ] Add some parameter to be able to take grammar restrictions.


- [ ] Support cvc5
	- [x] Add cvc5 tactic
	- [ ] Combine it with the veritAst branch
	- [ ] Support `forall_inst` from cvc5
	- [ ] Figure out spec of `all_simplify` and support it
	- [ ] cvc5 returns [false] in some certificates and [] in others. We can't handle [false].


The following are ideas and tasks that will move forward my thesis work. 
- [x] Check how SMTCoq deals with global and local parameters.
- [x] Read transformations paper to see if passing of particular hypotheses is allowed by sniper.
- [ ] What's the point of Alethe proofs? What benefit in ability do they provide? Read the related papers.
	- [x] Read about the epsilon calculus by reading Jeremy's chapter in the Stanford Encyclopedia.
- [ ] Read Chantal's ITP paper.
	- [ ] Can we skolemize existentials using a transformation for sniper?
- [ ] Grock abduction paper
- [ ] Abduction integration applications?
- [ ] Benchmarking via removing hypotheses in benchmarks?
	- [ ] Look at sets of Coq benchmarks
- [ ] Abduction might fit nicely into bit-vectors?
- [ ] Read comp reports
- [ ] Synthesis readings?



- Problem with `not_not`:
  Proofs currently using the `not_not` rule fail on the `th_resolution` 
  step following `not_not`. The rule specifies the following tautology:
	`(not (not (not x)), x)`
  It is used for example, as follows
  1. `~~x`
  2. `~~~x v x` `not_not`
  3. `x` `th_resolution 1,2`
  Currently, double negations aren't parsed as Fnot2, and are instead, implicitly simplified. So the above example is given to SMTCoq as:
  1. `x`
  2. `~x v x` `not_not`
  And then what is expected is:
  3. `x` `th_resolution 1,2`
  but instead, since `2` is a tautology, resolution has an optimization
  step that doesn't consider `2` at all (this didn't break things before 
  since there was no rule like `not_not`). So it constructs something
  different from `x` and this creates a problem.
  Solution 1: remove this optimization in resolution, but this seems
  to be hard to do.
  Solution 2: Parse double negations as `Fnot2` without simplifying
  (this is already done in commented code). The problem here is that 
  there are many rules for which SMTCoq takes the premise and constructs 
  a conclusion, and in this conclusion also. SMTCoq simplifies double 
  negations. So `1` above cant be guaranteed to produce `x` instead of 
  `~~x` unless all the rules that do this are changed (and there are 
  quite a few, for ex `equiv_pos2`).VC4 does not yet produce proof certificates for that


Dev Notes
- When adding/removing files to the project, 
	+ change /src/versions/standard/Makefile.local, /src/versions/standard/_CoqProject 
	+ then, generate the Coq makefile by running `coq_makefile -f _CoqProject -o Makefile` in /src/versions/standard/
	+ go back to src, `make clean` `.configure.sh`, and then `make`
- While debugging, run the coq file using coqc from the command-line as `coqc filename`, that will print the print statements from the OCaml code written as `Printf.printf "some-text".
- When the tactic complains that `no matching cases were found` for the verit tactic, unfold the verit tactic from:
	Tactic Notation "verit"           :=
	  prop2bool;
	  [ .. | let Hs := get_hyps in
	         match Hs with
	         | Some ?Hs =>
	           prop2bool_hyps Hs;
	           [ .. | verit_bool_base_auto (Some Hs) ]
	         | None => verit_bool_base_auto (@None nat)
	         end; vauto
	  ].
to:
	prop2bool.
	let Hs := get_hyps in idtac Hs.
	prop2bool_hyps H.
	verit_bool_base_auto (Some H).