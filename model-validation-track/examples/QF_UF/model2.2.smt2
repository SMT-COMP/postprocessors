sat
(
 (define-fun a () U (as @0 U))
 (define-fun b () V (as @1 V))
 (define-fun f ((x U)) U x)
 (define-fun g ((x U)) V (as @2 V))
 (define-fun h ((x V)) U (f (as @0 U)))
)