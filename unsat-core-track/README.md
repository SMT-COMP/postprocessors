## The Unsat-Core Track Post-Processor

The SMT Competition Unsat-Core Track post-processor takes as input
* a file with the solver responses to the [SMT-LIB v2](http://www.smt-lib.org)
commands `check-sat` and `get-unsat-core`  
(for examples, see file [test.out](test/test.out)
 as an example response to [test.smt2](test/test.smt2),
 and [here](http://smtlib.cs.uiowa.edu/examples.shtml))
* and the [SMT-LIB v2](http://www.smt-lib.org) file from which the unsat core
was constructed.

It checks if the solver response to `check-sat` is indeed `unsat` and
verifies that the unsat core returned in response to `get-unsat-core` is
unsatisfiable using a set of validating solvers built into the script.

### Setup

1. Unpack all [validation solvers](validation_solvers) and ensure that they
   are available at
```bash
./validation_solvers/<solver>/bin/<solver>
```
The solvers currently required by the script are `alt-ergo`, `bitwuzla`, `cvc4`, `mathsat`, `ultimateeliminator+mathsat`, `vampire`, `yices`, and `z3`.

2. Ensure that the [scrambler](https://github.com/SMT-COMP/scrambler) is in
the current directory as a compiled binary.

### Usage

```bash
$ ./process <solver-output> <path-to-benchmark>
```

There is test a case in directory [test](test).  Running an unsat core solver on
this file should result in output similar to [test/test.out](test/test.out).
To verify the output, call

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
