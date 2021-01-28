sat
(model 
  ;; universe for U:
  ;;   (as @val1 U) (as @val0 U) 
  (define-fun a () U
    (as @val0 U))
  (define-fun b () U
    (as @val1 U))
  (define-fun f ((x!0 U)) U
    (as @val1 U))
)
