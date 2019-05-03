;; Checking division by zero is handled correctly
(set-logic QF_BV)
(set-option :produce-models true)

(declare-const x_0 (_ BitVec 32))
(declare-const x_1 (_ BitVec 32))
(declare-const x_2 (_ BitVec 32))
(declare-const y_0 (_ BitVec 32))
(declare-const y_1 (_ BitVec 32))
(declare-const y_2 (_ BitVec 32))

(assert (= x_0 (bvudiv x_1 x_2)))
(assert (= y_0 (bvurem y_1 y_2)))
(assert (= x_2 (_ bv0 32)))
(assert (= y_2 (_ bv0 32)))
(check-sat)
(get-model)
(exit)
