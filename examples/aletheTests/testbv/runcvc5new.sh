#! /usr/bin/env bash

../../../../cvc5/cvc5/build/bin/cvc5 --dump-proofs --proof-prune-input --proof-format-mode=alethe --simplification=none --dag-thres=0 --lang=smt2 --proof-granularity=dsl-rewrite $1
