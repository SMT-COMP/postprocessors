sat
(model 
  (define-fun a () U
    (as @0 U))
  (define-fun b () U
    (as @1 U))
  (define-fun f ((@p0 U)) U
    (ite (= @p0 a) (as @1 U) (as @0 U))))