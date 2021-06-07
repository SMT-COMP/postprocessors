(set-logic QF_UF)
(declare-fun x () Bool)
(declare-fun y () Bool)
(declare-fun z () Bool)

(assert
 (and (or x y)
      (or (not x) y)
      (or x (not y))
      (or (not x) (not y))))
(assert
 (and (or y z)
      (or (not y) z)
      (or y (not z))
      (or (not y) (not z))))

(check-sat)
(exit)
