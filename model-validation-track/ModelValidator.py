
#def warn(*args, **kwargs):
#    pass
#import warnings
#warnings.warn = warn

#import warnings
#warnings.filterwarnings("ignore", category=DeprecationWarning)

from pysmt.shortcuts import read_smtlib, BV, Symbol, simplify
from pysmt.typing import BVType
from pysmt.smtlib.printers import to_smtlib
from pysmt.smtlib.parser import SmtLibParser, Tokenizer
from pysmt.exceptions import PysmtSyntaxError
from pysmt.walkers import IdentityDagWalker
import sys
import argparse
from os import path


""" Workaround for PysmtSyntaxError broken constructor"""
def newInit(self, message, pos_info=None):
    self.message = message
    self.pos_info = pos_info

PysmtSyntaxError.__init__ = newInit

class SymbolCollector(IdentityDagWalker):
    def __init__(self):
        IdentityDagWalker.__init__(self)
        self.symbols = set()

    def walk_symbol(self, formula, args, **kwargs):
        self.symbols.add(formula)
        return self.mgr.Symbol(formula.symbol_name(),
                               formula.symbol_type())


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

def readModel(parser, modelFile):
    with open(modelFile) as script:
        model = {}
        symbols = parser.env.formula_manager.symbols
        parser.cache.update(symbols)
        tokens = Tokenizer(script, interactive=parser.interactive)
        res = []
        current = tokens.consume()
        if (current != "sat"):
            raise PysmtSyntaxError("'sat' expected", tokens.pos_info)
        parser.consume_opening(tokens, "<main>")
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
    environment=parser.env
    with open(smtFile) as stream:
        script = parser.get_script(stream)
        formula = script.get_strict_formula()
        return formula

def checkFullModel(formula, model):
    symbolCollector = SymbolCollector()
    symbolCollector.walk(formula)
    if len(model) > len(symbolCollector.symbols):
        print ("INVALID: More variables in model than in input problem.")
        sys.exit(0)

    for symbol in symbolCollector.symbols:
        if not symbol in model:
            print ("INVALID: Missing model value for {}.".format(symbol.symbol_name()))
            sys.exit(0)

def validateModel(smtFile, modelFile):
    try:
        if (not path.exists(smtFile)):
            raise Exception("File not found: {}".format(smtFile))

        if (not path.exists(modelFile)):
            raise Exception("File not found: {}".format(modelFile))

        parser = SmtLibParser()

        formula = readSmtFile(parser, smtFile)
        model = readModel(parser, modelFile)

        checkFullModel(formula, model)

        result = simplify(formula.substitute(model))

        if (not result.is_constant()):
            print ("INVALID: Did not provide a full model.")
        elif (not result.is_true()):
            print ("INVALID: Model does not evaluate to true.")
        else:
            print ("VALID")
    except Exception as e:
        print(e)
        sys.exit(1)


class ArgParser(argparse.ArgumentParser):
    def error(self, message):
        sys.stderr.write('error: %s\n' % message)
        self.print_help()
        sys.exit(2)

parser = argparse.ArgumentParser(description='QF_BV Model validator.')
parser.add_argument('--smt2', type=str, help='SMT-LIB v2 benchmark', required = True)
parser.add_argument('--model', type=str, help='The full model returned by the SMT solver', required = True)

args = parser.parse_args()
validateModel(args.smt2, args.model)

