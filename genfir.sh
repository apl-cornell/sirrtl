#!/bin/bash
arg=$1
sbt -v "project genfir" "runMain solutions.FirrtlGenerator output $arg"
firrtl -i output/"$arg".fir -o output/"$arg".lbl.fir -z output/"$arg".z3 -X labeled
ERRORS=$(z3 -smt2 output/"$arg".z3 | grep "sat" | grep -v "unsat" | wc -l)
echo "Found $ERRORS errors in label checking"

