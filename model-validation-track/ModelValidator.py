#!/usr/bin/env python3

import sys
import argparse
from os import path

from pysmt.shortcuts import get_env
from pysmt.smtlib.parser import SmtLibParser, Tokenizer
from pysmt.exceptions import PysmtSyntaxError


def parseDefineFun(parser, tokens):
    current = tokens.consume()

    if (current != "define-fun"):
        raise PysmtSyntaxError("'define-fun' expected", tokens.pos_info)
    var = parser.get_expression(tokens)
    if (not var.is_symbol()):
        raise PysmtSyntaxError("Symbol expected", tokens.pos_info)
    namedparams = parser.parse_named_params(tokens, "define-fun")
    if (namedparams):
        raise PysmtSyntaxError("'()' expected", tokens.pos_info)
    rtype = parser.parse_type(tokens, "define-fun")
    ebody = parser.get_expression(tokens)
    if (not ebody.is_constant()):
        raise PysmtSyntaxError("Constant expected", tokens.pos_info)
    current = tokens.consume()
    return (var, ebody)


def readModel(parser, modelFile, inputFile):
    with open(modelFile) as script:
        model = {}
        symbols = parser.env.formula_manager.symbols
        parser.cache.update(symbols)
        tokens = Tokenizer(script, interactive=parser.interactive)
        res = []
        current = tokens.consume()

        if (current == "unknown"):
            print ("model_validator_status=UNKNOWN")
            print ("model_validator_error=solver_returned_unknown")
            sys.exit(0)
        if (current == "unsat"):
            status = None
            with open(inputFile, 'r') as infile:
                for line in infile:
                    if ":status" in line:
                        if "unsat" in line:
                            status = "unsat"
                            print ("model_validator_status=UNKNOWN")
                            print ("model_validator_error=the_problem_status_is_unsatisfiable")
                        elif "sat" in line:
                            status = "sat"
                            print ("model_validator_status=INVALID")
                            print ("model_validator_error=the_problem_status_is_satisfiable")
                        elif "unknown" in line:
                            print ("model_validator_status=UNKNOWN")
                            print ("model_validator_error=the_problem_status_is_unknown")
                            status = "unknown"
                        break
            # the benchmark scrambler removes the status line, in case of a
            # benchmark without status line we assume satisfiability
            if not status:
                print ("model_validator_status=INVALID")
                print ("model_validator_error=the_problem_has_no_status")
            sys.exit(0)
        if (current != "sat"):
            raise PysmtSyntaxError("'sat' expected", tokens.pos_info)
        # Return UNKNOWN if the output is only "sat" and does not contain a model
        try:
            current = tokens.consume_maybe()
        except StopIteration:
            print ("model_validator_status=UNKNOWN")
            print ("model_validator_error=no_output")
            sys.exit(0)

        if (current != "("):
            raise PysmtSyntaxError("'(' expected", tokens.pos_info)
        current = tokens.consume()
        if (current != "model"):
            raise PysmtSyntaxError("'model' expected", tokens.pos_info)

        current = tokens.consume()
        while current != ")":
            if (current != "("):
                raise PysmtSyntaxError("'(' expected", tokens.pos_info)
            (var, val) = parseDefineFun(parser, tokens)
            model[var] = val
            current = tokens.consume()
        return model


def readSmtFile(parser, smtFile):
    with open(smtFile) as stream:
        script = parser.get_script(stream)
        formula = script.get_strict_formula()
        return (formula, script.get_declared_symbols())


def checkFullModel(model, symbols):
    if len(model) > len(symbols):
        print ("model_validator_status=INVALID")
        print ("model_validator_error=more_variables_in_model_than_input")
        sys.exit(0)

    for symbol in symbols:
        if not symbol in model:
            print ("model_validator_status=INVALID")
            print ("model_validator_error=missing_model_value")
            sys.exit(0)


def validateModel(smtFile, modelFile, inputFile):
    try:
        if not path.exists(smtFile):
            raise Exception("File not found: {}".format(smtFile))

        if not path.exists(modelFile):
            raise Exception("File not found: {}".format(modelFile))

        if path.getsize(modelFile) == 0:
            print ("model_validator_status=UNKNOWN")
            print ("model_validator_error=no_output")
            sys.exit(0)

        parser = SmtLibParser()

        (formula, symbols) = readSmtFile(parser, smtFile)
        model = readModel(parser, modelFile, inputFile)

        checkFullModel(model, symbols)

        result = formula.substitute(model).simplify()
        if not result.is_constant():
            print ("model_validator_status=INVALID")
            print ("model_validator_error=not_full_model")
        elif not result.is_true():
            print ("model_validator_status=INVALID")
            print ("model_validator_error=model_does_not_evaluate_to_true")
        else:
            print ("model_validator_status=VALID")
            print ("model_validator_error=none")
            print ("starexec-result=sat")
    except Exception as e:
        print ("model_validator_status=INVALID")
        print ("model_validator_error=unhandled_exception")
        print ("model_validator_exception=\"{}\"".format(str(e).replace("'", "\\'").replace('"', '\\"').replace('\n',' ')))
        sys.exit(0)


def main():
    parser = argparse.ArgumentParser(description='Model validator for QF logics with bit-vectors and linear arithemetic.')
    parser.add_argument('--smt2', type=str,
                        help='SMT-LIB v2 benchmark',
                        required = True)
    parser.add_argument('--model', type=str,
                        help='The full model returned by the SMT solver',
                        required = True)

    args = parser.parse_args()
    validateModel(args.smt2, args.model, args.smt2)

try:
    main()
except Exception as e:
    print ("model_validator_status=INVALID")
    print ("model_validator_error=toplevel_unhandled_exception")
    print ("model_validator_exception=\"{}\"".format(str(e).replace("'", "\\'").replace('"', '\\"').replace('\n',' ')))
    sys.exit(0)
