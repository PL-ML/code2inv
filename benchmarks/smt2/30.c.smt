(set-logic LIA)

(declare-const x Int)
(declare-const x! Int)

(declare-const x_19 Int)
(declare-const x_14 Int)
(declare-const x_13 Int)

(define-fun inv-f((x Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((x Int)(x_13 Int)(x_14 Int)(x_19 Int)) Bool
  (and
    (= x x_13)
    (= x_13 100)
  )
)

(define-fun trans-f ((x Int)(x! Int)(x_13 Int)(x_14 Int)(x_19 Int)) Bool
  (or
    (and
      (= x_19 x)
      (= x_19 x!)
    )
    (and
      (= x_19 x)
      (> x_19 0)
      (= x_14 (- x_19 1))
      (= x_14 x!)
    )
  )
)

(define-fun post-f ((x Int)(x_13 Int)(x_14 Int)(x_19 Int)) Bool
  (or
    (not (= x x_19))
    (not
      (and
        (not (> x_19 0))
        (not (= x_19 0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f x x_13 x_14 x_19 )
    (inv-f x )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f x )
      (trans-f x x! x_13 x_14 x_19 )
    )
    (inv-f x! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f x )
    (post-f x x_13 x_14 x_19 )
  )
))

