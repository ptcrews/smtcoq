#!/usr/bin/python3

name = input('Enter file name without extension: ')

#Create SMT file
smtname = name + ".smt2"
fsmt = open(smtname, "w")
fsmt.write("(set-logic UFLIA)\n")
#n = input('Enter number of Boolean variables: ')
#vars = []
#for i in range(int(n)):
#  v = input('Enter variable number ' + (i+1) + ': ')
#  #vars.append(v)
#  fsmt.write("(declare-fun " + v + " () Bool)\n")
fsmt.write("(declare-fun x () Bool)\n")
fsmt.write("(declare-fun y () Bool)\n")

lhs = input('Enter parenthesized term for LHS of equivalence: ')
rhs = input('Enter parenthesized term for RHS of equivalence: ')
fsmt.write("(assert " + lhs + ")\n")
fsmt.write("(assert (not " + rhs + "))\n")
fsmt.write("(check-sat)\n")
fsmt.close()

#Create proof file
proofname = name + ".vtlog"
fproof = open(proofname, "w")
fproof.write("(assume h1 " + lhs + ")\n")
fproof.write("(assume h2 (not " + rhs + "))\n")
rname = input('Enter the name of the rewrite rule: ')
fproof.write("(step t3 (cl (= " + lhs + " " + rhs + ")) :rule " + rname + ")\n")
fproof.write("(step t4 (cl (not (= " + lhs + " " + rhs + ")) (not " + lhs + ") " + rhs + ") :rule equiv_pos2)\n")
fproof.write("(step t5 (cl) :rule resolution :premises (t4 t3 h2 h1))\n")
fproof.close()

#Create Coq file
coqname = "test" + name + ".v"
fcoq = open(coqname, "w")
fcoq.write("Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq.\n")
fcoq.write("Require Import SMTCoq.SMTCoq.\n")
fcoq.write("Require Import Bool.\n")
fcoq.write("Section Test" + name + "Debug.\n")
fcoq.write("  Verit_Checker\n")
fcoq.write("    \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/testrewrites/" + smtname + "\"\n")
fcoq.write("    \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/testrewrites/" + proofname + "\".\n")
fcoq.write("End Test" + name + "Debug.\n")
fcoq.close()
