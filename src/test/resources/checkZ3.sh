#!/bin/bash
file=$1
touch "$file".out
z3 -smt2 "$file" > "$file".out
FAILURE=$?
if [[ "$FAILURE" != 0 ]]
then
    echo "Z3 Exited with some failures and exit code $FAILURE. Skipping sat checking"
    exit -1
fi
ERRORS=$(grep "sat" "$file".out | grep -v "unsat" | wc -l)
echo "Found $ERRORS errors in label checking"
exit "$ERRORS"


