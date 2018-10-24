(set-logic LIA)

(declare-const j Int)
(declare-const j! Int)
(declare-const i Int)
(declare-const i! Int)

(declare-const j_22 Int)
(declare-const j_16 Int)
(declare-const j_14 Int)
(declare-const i_21 Int)
(declare-const i_15 Int)
(declare-const i_13 Int)

(define-fun inv-f((i Int)(j Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((i Int)(j Int)(i_13 Int)(i_15 Int)(i_21 Int)(j_14 Int)(j_16 Int)(j_22 Int)) Bool
  (and
    (= j j_14)
    (= i i_13)
    (= i_13 1)
    (= j_14 20)
  )
)

(define-fun trans-f ((i Int)(j Int)(i! Int)(j! Int)(i_13 Int)(i_15 Int)(i_21 Int)(j_14 Int)(j_16 Int)(j_22 Int)) Bool
  (or
    (and
      (= i_21 i)
      (= j_22 j)
      (= j_22 j!)
      (= i_21 i!)
    )
    (and
      (= i_21 i)
      (= j_22 j)
      (>= j_22 i_21)
      (= i_15 (+ i_21 2))
      (= j_16 (- j_22 1))
      (= j_16 j!)
      (= i_15 i!)
    )
  )
)

(define-fun post-f ((i Int)(j Int)(i_13 Int)(i_15 Int)(i_21 Int)(j_14 Int)(j_16 Int)(j_22 Int)) Bool
  (or
    (not
      (and
        (= i i_21)
        (= j j_22)
      )
    )
    (not
      (and
        (not (>= j_22 i_21))
        (not (= j_22 13))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f i j i_13 i_15 i_21 j_14 j_16 j_22 )
    (inv-f i j )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f i j )
      (trans-f i j i! j! i_13 i_15 i_21 j_14 j_16 j_22 )
    )
    (inv-f i! j! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f i j )
    (post-f i j i_13 i_15 i_21 j_14 j_16 j_22 )
  )
))

