(set-logic LIA)

(declare-const y Int)
(declare-const y! Int)
(declare-const x Int)
(declare-const x! Int)
(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const lock Int)
(declare-const lock! Int)

(declare-const y_34 Int)
(declare-const y_26 Int)
(declare-const y_0 Int)
(declare-const x_33 Int)
(declare-const x_25 Int)
(declare-const x_23 Int)
(declare-const x_19 Int)
(declare-const lock_31 Int)
(declare-const lock_24 Int)
(declare-const lock_22 Int)
(declare-const lock_20 Int)

(define-fun inv-f((lock Int)(tmp Int)(x Int)(y Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((lock Int)(tmp Int)(x Int)(y Int)(lock_20 Int)(lock_22 Int)(lock_24 Int)(lock_31 Int)(x_19 Int)(x_23 Int)(x_25 Int)(x_33 Int)(y_0 Int)(y_26 Int)(y_34 Int)) Bool
  (and
    (= y y_0)
    (= x x_19)
    (= lock lock_20)
    (= x_19 y_0)
    (= lock_20 1)
  )
)

(define-fun trans-f ((lock Int)(tmp Int)(x Int)(y Int)(lock! Int)(tmp! Int)(x! Int)(y! Int)(lock_20 Int)(lock_22 Int)(lock_24 Int)(lock_31 Int)(x_19 Int)(x_23 Int)(x_25 Int)(x_33 Int)(y_0 Int)(y_26 Int)(y_34 Int)) Bool
  (or
    (and
      (= lock_31 lock)
      (= x_33 x)
      (= y_34 y)
      (= y_34 y!)
      (= x_33 x!)
      (= lock_31 lock!)
      (= tmp tmp!)
      (= lock lock!)
    )
    (and
      (= lock_31 lock)
      (= x_33 x)
      (= y_34 y)
      (not (= x_33 y_34))
      (= lock_24 0)
      (= x_25 y_34)
      (= y_26 (+ y_34 1))
      (= y_26 y!)
      (= x_25 x!)
      (= lock_24 lock!)
      (= tmp tmp!)
    )
    (and
      (= lock_31 lock)
      (= x_33 x)
      (= y_34 y)
      (not (= x_33 y_34))
      (= lock_22 1)
      (= x_23 y_34)
      (= y_34 y!)
      (= x_23 x!)
      (= lock_22 lock!)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((lock Int)(tmp Int)(x Int)(y Int)(lock_20 Int)(lock_22 Int)(lock_24 Int)(lock_31 Int)(x_19 Int)(x_23 Int)(x_25 Int)(x_33 Int)(y_0 Int)(y_26 Int)(y_34 Int)) Bool
  (or
    (not
      (and
        (= lock lock_31)
        (= x x_33)
        (= y y_34)
      )
    )
    (not
      (and
        (not (not (= x_33 y_34)))
        (not (= lock_31 1))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f lock tmp x y lock_20 lock_22 lock_24 lock_31 x_19 x_23 x_25 x_33 y_0 y_26 y_34 )
    (inv-f lock tmp x y )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f lock tmp x y )
      (trans-f lock tmp x y lock! tmp! x! y! lock_20 lock_22 lock_24 lock_31 x_19 x_23 x_25 x_33 y_0 y_26 y_34 )
    )
    (inv-f lock! tmp! x! y! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f lock tmp x y )
    (post-f lock tmp x y lock_20 lock_22 lock_24 lock_31 x_19 x_23 x_25 x_33 y_0 y_26 y_34 )
  )
))

