## The unsat core track post-processor

The SMT Competition unsat core track post-processor takes as input an
unsat core (see an example of the format in
[here](http://smtlib.cs.uiowa.edu/examples.shtml)) and the smt2 file
from which the unsat core is constructed, and verifies that the unsat
core is unsatisfiable using a set of validating solvers built into the
script.

### Setup

1. Ensure that the validating solvers are available at

```bash
./validation_solvers/<solver>/bin/<solver>
```

The solvers required by the script at the moment are `cvc4`, `mathsat`,
`z3`, and `vampire`.

2. Ensure that the [scrambler](https://github.com/SMT-COMP/scrambler) is in
the current directory as a compiled binary.

### Usage

```bash
$ ./process <solver-output> <path-to-benchmark>
```

There is test a case in `./test/`.  Running an unsat core solver on
this file should result in output similar to `./test/test.out`.

To verify the output, type

```bash
$ ./process ./test/test.out ./test/test.smt2
```

The output should be as follows

```
ucpp-version=2018v5
check-sat-result-is-erroneous=0
starexec-result=unsat
number-of-assert-commands=15
parsable-unsat-core=true
size-unsat-core=10
validation-solvers=3
validation-check-sat-result_cvc4=unsat
validation-check-sat-time_cvc4=0
validation-check-sat-result_mathsat=unsat
validation-check-sat-time_mathsat=0
validation-check-sat-result_z3=unsat
validation-check-sat-time_z3=0
unsat-core-rejections=0
unsat-core-confirmations=3
unsat-core-validated=true
result-is-erroneous=0
reduction=5
```
