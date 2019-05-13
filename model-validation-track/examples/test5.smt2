;; Checking that INVALID is returned if the solver returns unsat
(set-logic QF_BV)
(set-option :produce-models true)

(declare-const x_0 (_ BitVec 32))
(declare-const x_1 (_ BitVec 32))
(declare-const x_2 (_ BitVec 32))
(declare-const y_0 (_ BitVec 32))
(declare-const y_1 (_ BitVec 32))
(declare-const y_2 (_ BitVec 32))

(assert (= x_0 x_1))
(assert (bvult x_0 x_1))
(check-sat)
(get-model)
(exit)
