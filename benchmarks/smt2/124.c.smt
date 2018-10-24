(set-logic LIA)

(declare-const y Int)
(declare-const y! Int)
(declare-const x Int)
(declare-const x! Int)
(declare-const j Int)
(declare-const j! Int)
(declare-const i Int)
(declare-const i! Int)

(declare-const y_25 Int)
(declare-const y_19 Int)
(declare-const y_0 Int)
(declare-const x_24 Int)
(declare-const x_18 Int)
(declare-const x_0 Int)
(declare-const j_17 Int)
(declare-const i_16 Int)

(define-fun inv-f((i Int)(j Int)(x Int)(y Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((i Int)(j Int)(x Int)(y Int)(i_16 Int)(j_17 Int)(x_0 Int)(x_18 Int)(x_24 Int)(y_0 Int)(y_19 Int)(y_25 Int)) Bool
  (and
    (= y y_0)
    (= x x_0)
    (= j j_17)
    (= i i_16)
    (= i_16 x_0)
    (= j_17 y_0)
  )
)

(define-fun trans-f ((i Int)(j Int)(x Int)(y Int)(i! Int)(j! Int)(x! Int)(y! Int)(i_16 Int)(j_17 Int)(x_0 Int)(x_18 Int)(x_24 Int)(y_0 Int)(y_19 Int)(y_25 Int)) Bool
  (or
    (and
      (= x_24 x)
      (= y_25 y)
      (= y_25 y!)
      (= x_24 x!)
      (= y y!)
      (= j j!)
      (= i i!)
    )
    (and
      (= x_24 x)
      (= y_25 y)
      (not (= x_24 0))
      (= x_18 (- x_24 1))
      (= y_19 (- y_25 1))
      (= y_19 y!)
      (= x_18 x!)
      (= j j!)
      (= i i!)
    )
  )
)

(define-fun post-f ((i Int)(j Int)(x Int)(y Int)(i_16 Int)(j_17 Int)(x_0 Int)(x_18 Int)(x_24 Int)(y_0 Int)(y_19 Int)(y_25 Int)) Bool
  (or
    (not
      (and
        (= i i_16)
        (= j j_17)
        (= x x_24)
        (= y y_25)
      )
    )
    (not
      (and
        (not (not (= x_24 0)))
        (= i_16 j_17)
        (not (= y_25 0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f i j x y i_16 j_17 x_0 x_18 x_24 y_0 y_19 y_25 )
    (inv-f i j x y )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f i j x y )
      (trans-f i j x y i! j! x! y! i_16 j_17 x_0 x_18 x_24 y_0 y_19 y_25 )
    )
    (inv-f i! j! x! y! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f i j x y )
    (post-f i j x y i_16 j_17 x_0 x_18 x_24 y_0 y_19 y_25 )
  )
))

