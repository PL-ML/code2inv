(set-logic LIA)

(declare-const y Int)
(declare-const y! Int)
(declare-const x Int)
(declare-const x! Int)

(declare-const y_0 Int)
(declare-const x_19 Int)
(declare-const x_14 Int)
(declare-const x_13 Int)

(define-fun inv-f((x Int)(y Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((x Int)(y Int)(x_13 Int)(x_14 Int)(x_19 Int)(y_0 Int)) Bool
  (and
    (= x x_13)
    (= x_13 1)
  )
)

(define-fun trans-f ((x Int)(y Int)(x! Int)(y! Int)(x_13 Int)(x_14 Int)(x_19 Int)(y_0 Int)) Bool
  (or
    (and
      (= x_19 x)
      (= x_19 x!)
      (= y y_0)
      (= y! y_0)
    )
    (and
      (= x_19 x)
      (< x_19 y_0)
      (= x_14 (+ x_19 x_19))
      (= x_14 x!)
      (= y y_0)
      (= y! y_0)
    )
  )
)

(define-fun post-f ((x Int)(y Int)(x_13 Int)(x_14 Int)(x_19 Int)(y_0 Int)) Bool
  (or
    (not
      (and
        (= x x_19)
        (= y y_0)
      )
    )
    (not
      (and
        (not (< x_19 y_0))
        (not (>= x_19 1))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f x y x_13 x_14 x_19 y_0 )
    (inv-f x y )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f x y )
      (trans-f x y x! y! x_13 x_14 x_19 y_0 )
    )
    (inv-f x! y! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f x y )
    (post-f x y x_13 x_14 x_19 y_0 )
  )
))

