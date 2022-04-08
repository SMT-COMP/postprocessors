#!/bin/sh
#
# check if the test files in test/sat, test/unsat, test/starexec-unknown
# produce the corresponding expected results.

for file in test/*.txt; do
    expected=${file%.txt}.expected
    ./process "$file" | diff ${expected} - || echo "... in $file"
done
