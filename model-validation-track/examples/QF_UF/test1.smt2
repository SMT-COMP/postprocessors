(set-option :produce-models true)
(set-logic QF_UF)

(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)

(assert (not (= a b)))
(assert (= (f a) b))
(assert (= (f b) a))

(check-sat)
(get-model)
