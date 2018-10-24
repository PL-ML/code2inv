(set-logic LIA)

(declare-const y Int)
(declare-const y! Int)
(declare-const x Int)
(declare-const x! Int)
(declare-const n Int)
(declare-const n! Int)

(declare-const y_24 Int)
(declare-const y_17 Int)
(declare-const y_0 Int)
(declare-const x_23 Int)
(declare-const x_18 Int)
(declare-const x_16 Int)
(declare-const n_0 Int)

(define-fun inv-f((n Int)(x Int)(y Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((n Int)(x Int)(y Int)(n_0 Int)(x_16 Int)(x_18 Int)(x_23 Int)(y_0 Int)(y_17 Int)(y_24 Int)) Bool
  (and
    (= x x_16)
    (= x_16 1)
  )
)

(define-fun trans-f ((n Int)(x Int)(y Int)(n! Int)(x! Int)(y! Int)(n_0 Int)(x_16 Int)(x_18 Int)(x_23 Int)(y_0 Int)(y_17 Int)(y_24 Int)) Bool
  (or
    (and
      (= x_23 x)
      (= y_24 y)
      (= y_24 y!)
      (= x_23 x!)
      (= n n_0)
      (= n! n_0)
      (= y y!)
    )
    (and
      (= x_23 x)
      (= y_24 y)
      (<= x_23 n_0)
      (= y_17 (- n_0 x_23))
      (= x_18 (+ x_23 1))
      (= y_17 y!)
      (= x_18 x!)
      (= n n_0)
      (= n! n_0)
    )
  )
)

(define-fun post-f ((n Int)(x Int)(y Int)(n_0 Int)(x_16 Int)(x_18 Int)(x_23 Int)(y_0 Int)(y_17 Int)(y_24 Int)) Bool
  (or
    (not
      (and
        (= n n_0)
        (= x x_23)
        (= y y_24)
      )
    )
    (not
      (and
        (not (<= x_23 n_0))
        (> n_0 0)
        (not (< y_24 n_0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f n x y n_0 x_16 x_18 x_23 y_0 y_17 y_24 )
    (inv-f n x y )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f n x y )
      (trans-f n x y n! x! y! n_0 x_16 x_18 x_23 y_0 y_17 y_24 )
    )
    (inv-f n! x! y! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f n x y )
    (post-f n x y n_0 x_16 x_18 x_23 y_0 y_17 y_24 )
  )
))

