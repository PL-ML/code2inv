(set-logic HORN)

(set-option :produce-proofs true)
(set-option :produce-models true)
(declare-fun itp ( Int Int ) Bool)

;(define-fun itp ( (x!1 Int) (x!2 Int) ) Bool
; (<= 0 x!1)
;)
;(define-fun itp ( (x!1 Int) (x!2 Int) ) Bool
; (<= (* x!2 x!2) (+ x!1 x!1))
;)
;

; A = 0
; assume (A < B)

(assert
  (forall ( (s Int) (i Int) ) 
    (=>
      (and (= s 1) (= i 0))
      (itp s i)
    )
  )
)

; i += 1
; s += i;

(assert
  (forall ( (s Int) (i Int) (s2 Int) (i2 Int) ) 
    (=>
      (and
        (itp s i)
        (= i2 (+ i 1))
        (= s2 (+ s i2))
      )
      (itp s2 i2)
    )
  )
)

; sassert p: s + s >= i * i
; inv => p
; inv /\ not p => false

;(assert
;  (forall ( (s Int) (i Int) ) 
;    (=> (itp s i)
;      (<= (* i i) (+ s s))
;    )
;  )
;)

(assert
  (forall ( (s Int) (i Int) ) 
    (=> 
      (and
        (itp s i)
        (> (* i i) (+ s s))
      )
      false
    )
  )
)


;(assert
;  (forall ( (A Int) (B Int) ) 
;    (=>
;      (and
;        (itp A B)
;        (< 10 A)
;        (<= B 20)
;      )
;      false
;    )
;  )
;)

(check-sat)
;(get-model)
(get-proof)
;(exit)
