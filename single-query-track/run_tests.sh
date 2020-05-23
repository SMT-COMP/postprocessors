#!/bin/sh
#
# check if the test files in test/sat, test/unsat, test/starexec-unknown
# produce the corresponding expected results.

for result in sat unsat starexec-unknown; do
    echo "starexec-result=$result" > expected.txt
    for file in test/$result/*; do
	./process "$file" | diff expected.txt - || echo "... in $file"
    done
    rm expected.txt
done
