#!/bin/bash

function get_abs_path {
  echo $(cd $(dirname $1); pwd)
}

SCRIPTDIR=$(get_abs_path $0)

SCRAMBLER=${SCRIPTDIR}/scrambler
TESTSOLVER=${SCRIPTDIR}/validation_solvers/z3/bin/z3

tmpdir=$(mktemp -d)

errors=false

for file in test_positive/*.smt2; do
    corescript=${tmpdir}/$(basename $file .smt2)-uc.smt2
    coreoutput=${tmpdir}/$(basename $file .smt2)-uc.res
    ${SCRAMBLER} -gen-unsat-core true < $file > ${corescript}
    ${TESTSOLVER} ${corescript} > ${coreoutput}
    nconfs=$(\
        ./process ${coreoutput} ${corescript} \
        |sed -n 's/unsat-core-confirmations=\([0-9][0-9]*\)/\1/p'
    )
    if [[ ${nconfs} != 3 ]]; then
        echo "Failed to verify ${file}"
        errors=true
    fi
done

for file in test_negative/*-uc.smt2; do
    corescript=${file}
    coreoutput=$(dirname ${file})/$(basename ${file} .smt2).res
    nconfs=$(\
        ./process ${coreoutput} ${corescript} \
        |sed -n 's/unsat-core-rejections=\([0-9][0-9]*\)/\1/p'
    )
    if [[ ${nconfs} != 3 ]]; then
        echo "Failed to reject ${file}"
        errors=true
    fi
done

for file in test_validation/*.smt2; do
    corescript=${file}
    coreoutput=$(dirname ${file})/$(basename ${file} .smt2).res
    expected=$(dirname ${file})/$(basename ${file} .smt2).expect
    if [[ "$(./process ${coreoutput} ${corescript} | grep -v 'ucpp-version=' | \
	    diff -q $expected -)" ]] ; then
        echo "Unexpected output for ${file}"
        errors=true
    fi
done


if [[ "${errors}" != false ]]; then
    echo "There were errors: see ${tmpdir}"
    exit 1
fi

rm -rf ${tmpdir}

