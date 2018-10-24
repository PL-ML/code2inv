(set-logic LIA)

(declare-const x Int)
(declare-const x! Int)
(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const sn Int)
(declare-const sn! Int)

(declare-const x_29 Int)
(declare-const x_21 Int)
(declare-const x_19 Int)
(declare-const sn_27 Int)
(declare-const sn_22 Int)
(declare-const sn_18 Int)

(define-fun inv-f((sn Int)(tmp Int)(x Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((sn Int)(tmp Int)(x Int)(sn_18 Int)(sn_22 Int)(sn_27 Int)(x_19 Int)(x_21 Int)(x_29 Int)) Bool
  (and
    (= x x_19)
    (= sn sn_18)
    (= sn_18 0)
    (= x_19 0)
  )
)

(define-fun trans-f ((sn Int)(tmp Int)(x Int)(sn! Int)(tmp! Int)(x! Int)(sn_18 Int)(sn_22 Int)(sn_27 Int)(x_19 Int)(x_21 Int)(x_29 Int)) Bool
  (or
    (and
      (= sn_27 sn)
      (= x_29 x)
      (= x_29 x!)
      (= sn_27 sn!)
      (= x x!)
      (= tmp tmp!)
      (= sn sn!)
    )
    (and
      (= sn_27 sn)
      (= x_29 x)
      (= x_21 (+ x_29 1))
      (= sn_22 (+ sn_27 1))
      (= x_21 x!)
      (= sn_22 sn!)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((sn Int)(tmp Int)(x Int)(sn_18 Int)(sn_22 Int)(sn_27 Int)(x_19 Int)(x_21 Int)(x_29 Int)) Bool
  (or
    (not
      (and
        (= sn sn_27)
        (= x x_29)
      )
    )
    (not
      (and
        (not (= sn_27 x_29))
        (not (= sn_27 -1))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f sn tmp x sn_18 sn_22 sn_27 x_19 x_21 x_29 )
    (inv-f sn tmp x )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f sn tmp x )
      (trans-f sn tmp x sn! tmp! x! sn_18 sn_22 sn_27 x_19 x_21 x_29 )
    )
    (inv-f sn! tmp! x! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f sn tmp x )
    (post-f sn tmp x sn_18 sn_22 sn_27 x_19 x_21 x_29 )
  )
))

