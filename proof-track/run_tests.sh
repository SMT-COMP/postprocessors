#!/bin/sh
#
# check if the test files in test/sat, test/unsat, test/starexec-unknown
# produce the corresponding expected results.

for file in test/*.txt; do
    expected=${file%.txt}.expected
    ./process "$file" > test.out || echo "post-processor error in $file"
    diff ${expected} test.out || echo "... in $file"
    rm test.out
done
