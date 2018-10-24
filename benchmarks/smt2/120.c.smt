(set-logic LIA)

(declare-const sn Int)
(declare-const sn! Int)
(declare-const i Int)
(declare-const i! Int)

(declare-const sn_25 Int)
(declare-const sn_19 Int)
(declare-const sn_16 Int)
(declare-const i_24 Int)
(declare-const i_18 Int)
(declare-const i_17 Int)

(define-fun inv-f((i Int)(sn Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((i Int)(sn Int)(i_17 Int)(i_18 Int)(i_24 Int)(sn_16 Int)(sn_19 Int)(sn_25 Int)) Bool
  (and
    (= sn sn_16)
    (= i i_17)
    (= sn_16 0)
    (= i_17 1)
  )
)

(define-fun trans-f ((i Int)(sn Int)(i! Int)(sn! Int)(i_17 Int)(i_18 Int)(i_24 Int)(sn_16 Int)(sn_19 Int)(sn_25 Int)) Bool
  (or
    (and
      (= i_24 i)
      (= sn_25 sn)
      (= sn_25 sn!)
      (= i_24 i!)
      (= sn sn!)
    )
    (and
      (= i_24 i)
      (= sn_25 sn)
      (<= i_24 8)
      (= i_18 (+ i_24 1))
      (= sn_19 (+ sn_25 1))
      (= sn_19 sn!)
      (= i_18 i!)
    )
  )
)

(define-fun post-f ((i Int)(sn Int)(i_17 Int)(i_18 Int)(i_24 Int)(sn_16 Int)(sn_19 Int)(sn_25 Int)) Bool
  (or
    (not
      (and
        (= i i_24)
        (= sn sn_25)
      )
    )
    (not
      (and
        (not (<= i_24 8))
        (not (= sn_25 8))
        (not (= sn_25 0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f i sn i_17 i_18 i_24 sn_16 sn_19 sn_25 )
    (inv-f i sn )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f i sn )
      (trans-f i sn i! sn! i_17 i_18 i_24 sn_16 sn_19 sn_25 )
    )
    (inv-f i! sn! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f i sn )
    (post-f i sn i_17 i_18 i_24 sn_16 sn_19 sn_25 )
  )
))

