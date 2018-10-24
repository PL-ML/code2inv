(set-logic LIA)

(declare-const x Int)
(declare-const x! Int)
(declare-const n Int)
(declare-const n! Int)

(declare-const x_22 Int)
(declare-const x_17 Int)
(declare-const x_15 Int)
(declare-const n_0 Int)

(define-fun inv-f((n Int)(x Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((n Int)(x Int)(n_0 Int)(x_15 Int)(x_17 Int)(x_22 Int)) Bool
  (and
    (= x x_15)
    (= n n_0)
    (= x_15 0)
    (>= n_0 0)
  )
)

(define-fun trans-f ((n Int)(x Int)(n! Int)(x! Int)(n_0 Int)(x_15 Int)(x_17 Int)(x_22 Int)) Bool
  (or
    (and
      (= x_22 x)
      (= x_22 x!)
      (= n n_0)
      (= n! n_0)
    )
    (and
      (= x_22 x)
      (< x_22 n_0)
      (= x_17 (+ x_22 1))
      (= x_17 x!)
      (= n n_0)
      (= n! n_0)
    )
  )
)

(define-fun post-f ((n Int)(x Int)(n_0 Int)(x_15 Int)(x_17 Int)(x_22 Int)) Bool
  (or
    (not
      (and
        (= n n_0)
        (= x x_22)
      )
    )
    (not
      (and
        (not (< x_22 n_0))
        (not (= x_22 n_0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f n x n_0 x_15 x_17 x_22 )
    (inv-f n x )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f n x )
      (trans-f n x n! x! n_0 x_15 x_17 x_22 )
    )
    (inv-f n! x! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f n x )
    (post-f n x n_0 x_15 x_17 x_22 )
  )
))

