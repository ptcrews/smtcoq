#!/usr/bin/python3
import csv

with open('rewrites.csv') as csv_file:
  csv_reader = csv.reader(csv_file, delimiter=',')
  for row in csv_reader:
    name = row[0]
    #Create SMT file
    smtname = "./smt/" + name + ".smt2"
    fsmt = open(smtname, "w")
    fsmt.write("(set-logic UFLIA)\n")
    fsmt.write("(declare-fun x () Bool)\n")
    fsmt.write("(declare-fun y () Bool)\n")

    lhs = row[1]
    rhs = row[2]
    fsmt.write("(assert " + lhs + ")\n")
    fsmt.write("(assert (not " + rhs + "))\n")
    fsmt.write("(check-sat)\n")
    fsmt.close()

    #Create proof file
    proofname = "./proof/" + name + ".vtlog"
    fproof = open(proofname, "w")
    fproof.write("(assume h1 " + lhs + ")\n")
    fproof.write("(assume h2 (not " + rhs + "))\n")
    rname = row[3]
    fproof.write("(step t3 (cl (= " + lhs + " " + rhs + ")) :rule " + rname + ")\n")
    fproof.write("(step t4 (cl (not (= " + lhs + " " + rhs + ")) (not " + lhs + ") " + rhs + ") :rule equiv_pos2)\n")
    fproof.write("(step t5 (cl) :rule resolution :premises (t4 t3 h2 h1))\n")
    fproof.close()

    #Create Coq file
    coqname = "./coq/" + "test" + name + ".v"
    fcoq = open(coqname, "w")
    fcoq.write("Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq.\n")
    fcoq.write("Require Import SMTCoq.SMTCoq.\n")
    fcoq.write("Require Import Bool.\n")
    fcoq.write("Section Test" + name + "Debug.\n")
    fcoq.write("  Verit_Checker\n")
    coqsmtpath = "\"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/testrewrites/smt/" + name + ".smt2\""
    coqproofpath = "\"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/testrewrites/proof/" + name + ".vtlog\"."
    fcoq.write("    " + coqsmtpath + "\n")
    fcoq.write("    " + coqproofpath + "\n")
    fcoq.write("End Test" + name + "Debug.\n")
    fcoq.close()