(set-option :print-success false)
(set-option :produce-models true)
(set-info :status sat)
(set-info :category "crafted")
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (< x 0))
(check-sat)
(get-model)
(exit)
