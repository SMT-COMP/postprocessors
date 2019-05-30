import sys
import subprocess
from os.path import join as path_join

UNKNOWN_TEST_CASES = [
    ("test0.smt2", "model0.empty.smt2"),
    ("test4.smt2", "model4.unknown.smt2"),
    ("test6.smt2", "model4.unknown.smt2"),
    ("test6.smt2", "model0.empty.smt2"),
    ("test4.smt2", "model4.sat-no-model.smt2"),
]

VALID_TEST_CASES = [
    ("test1.smt2", "model1.cvc4.smt2"),
    ("test1.smt2", "model1.z3.smt2"),
    ("test1let.smt2", "model1.cvc4.smt2"),
    ("test1let.smt2", "model1.z3.smt2"),
    ("test2.smt2", "model2.cvc4.smt2"),
    ("test3.smt2", "model3.cvc4.smt2"),
    ("test6.smt2", "model6.smt2"),
    ("test7.smt2", "model7.smt2"),
    ("test8.smt2", "model8.smt2"),
    ("test10.smt2", "model10.smt2"),
]

INVALID_TEST_CASES = [
    ("test2.smt2", "model2.smt2"),
    ("test2.smt2", "model2.z3.smt2"),
    ("test3.smt2", "model3.z3.smt2"),
    ("test4.smt2", "model4.smt2"),
    ("test4.smt2", "model4.malformed.smt2"),
    ("test5.smt2", "model5.cvc4.smt2"),
    ("test5.smt2", "model5.z3.smt2"),
    ("test5.smt2", "model6.unsat.smt2"),
    ("test6.smt2", "model6.unsat.smt2"),
    ("test6.smt2", "model5.cvc4.smt2"),
    ("test6.smt2", "model5.z3.smt2"),
    ("test1.bool.smt2", "model1.bool.smt2"),
]

BASE_DIR = "examples/"

def validate(problem, model, result):
    interpreter = sys.executable
    args = [interpreter, "ModelValidator.py",
            "--smt2", problem,
            "--model", model]
    res = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    msg = res.stdout.decode('ascii')
    return msg.startswith("model_validator_status="+result), msg

for problem, model in UNKNOWN_TEST_CASES:
    print("testing UNKNOWN problem {} with model {}...".format(problem, model))
    res, msg = validate(path_join(BASE_DIR, problem),
                   path_join(BASE_DIR, model), "UNKNOWN")
    assert res, (problem, model, msg)
    print("OK")

for problem, model in VALID_TEST_CASES:
    print("testing VALID problem {} with model {}...".format(problem, model))
    res, msg = validate(path_join(BASE_DIR, problem),
                   path_join(BASE_DIR, model), "VALID")
    assert res, (problem, model, msg)
    print("OK")

for problem, model in INVALID_TEST_CASES:
    print("testing INVALID problem {} with model {}...".format(problem, model))
    res, msg = validate(path_join(BASE_DIR, problem),
                        path_join(BASE_DIR, model), "INVALID")
    assert res, (problem, model, msg)
    print("OK")
