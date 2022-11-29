#!/usr/bin/python3

n = input('Enter test file number: ')
fname = "test" + n + "debug.v"
f = open(fname, "w")
f.write("Require Import SMTCoq.SMTCoq.\n")
f.write("Require Import Bool.\n")
f.write("Require Import Int31.\n")
f.write("Local Open Scope int31_scope.\n\n")
f.write("Section Test" + n + "Debug.\n")
f.write("  Parse_certif_verit t_i" + n + " t_func" + n + " t_atom" + n + " t_form" + n + " root" + n + " used_roots" + n + " trace" + n + "\n")
f.write("End Test" + n + "Debug.\n")
f.close()
