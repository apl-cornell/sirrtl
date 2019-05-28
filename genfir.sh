#!/bin/bash
arg=$1
sbt -v "project genfir" "runMain solutions.FirrtlGenerator output $arg"
utils/bin/firrtl -i output/"$arg".fir -o output/"$arg".lbl.fir -z output/"$arg".z3 -X labeled
z3 -smt2 output/"$arg".z3 > output/"$arg".out
FAILURE=$?
if [[ "$FAILURE" != 0 ]]
then
    echo "Z3 Exited with some failures and exit code $FAILURE. Skipping sat checking"
    exit 1
fi
ERRORS=$(grep "sat" output/"$arg".out | grep -v "unsat" | wc -l)
echo "Found $ERRORS errors in label checking"

