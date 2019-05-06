import sys
import subprocess
from os.path import join as path_join

VALID_TEST_CASES = [
    ("test1.smt2", "model1.cvc4.smt2"),
    ("test1.smt2", "model1.z3.smt2"),
    ("test1let.smt2", "model1.cvc4.smt2"),
    ("test1let.smt2", "model1.z3.smt2"),
    ("test2.smt2", "model2.cvc4.smt2"),
    ("test3.smt2", "model3.cvc4.smt2"),
]

INVALID_TEST_CASES = [
    ("test2.smt2", "model2.smt2"),
    ("test2.smt2", "model2.z3.smt2"),
    ("test3.smt2", "model3.z3.smt2"),
    ("test4.smt2", "model4.smt2"),
]

BASE_DIR = "examples/"

def validate(problem, model):
    interpreter = sys.executable
    args = [interpreter, "ModelValidator.py",
            "--smt2", problem,
            "--model", model]
    res = subprocess.run(args, capture_output=True)
    msg = res.stdout.decode('ascii')
    return msg.startswith("VALID"), msg

for problem, model in VALID_TEST_CASES:
    res, msg = validate(path_join(BASE_DIR, problem),
                   path_join(BASE_DIR, model))
    assert res, (problem, model, msg)

for problem, model in INVALID_TEST_CASES:
    res, msg = validate(path_join(BASE_DIR, problem),
                        path_join(BASE_DIR, model))
    assert not res, (problem, model, msg)
