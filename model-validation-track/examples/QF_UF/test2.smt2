(set-option :produce-models true)
(set-logic QF_UF)

(declare-sort U 0)
(declare-sort V 0)
(declare-const a U)
(declare-const b V)
(declare-fun f (U) U)
(declare-fun g (U) V)
(declare-fun h (V) U)

(check-sat)
(get-model)
