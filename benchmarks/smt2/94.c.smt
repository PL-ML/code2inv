(set-logic LIA)

(declare-const n Int)
(declare-const n! Int)
(declare-const k Int)
(declare-const k! Int)
(declare-const j Int)
(declare-const j! Int)
(declare-const i Int)
(declare-const i! Int)

(declare-const n_0 Int)
(declare-const k_0 Int)
(declare-const j_28 Int)
(declare-const j_22 Int)
(declare-const j_20 Int)
(declare-const i_27 Int)
(declare-const i_21 Int)
(declare-const i_19 Int)

(define-fun inv-f((i Int)(j Int)(k Int)(n Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((i Int)(j Int)(k Int)(n Int)(i_19 Int)(i_21 Int)(i_27 Int)(j_20 Int)(j_22 Int)(j_28 Int)(k_0 Int)(n_0 Int)) Bool
  (and
    (= n n_0)
    (= k k_0)
    (= j j_20)
    (= i i_19)
    (>= k_0 0)
    (>= n_0 0)
    (= i_19 0)
    (= j_20 0)
  )
)

(define-fun trans-f ((i Int)(j Int)(k Int)(n Int)(i! Int)(j! Int)(k! Int)(n! Int)(i_19 Int)(i_21 Int)(i_27 Int)(j_20 Int)(j_22 Int)(j_28 Int)(k_0 Int)(n_0 Int)) Bool
  (or
    (and
      (= i_27 i)
      (= j_28 j)
      (= j_28 j!)
      (= i_27 i!)
      (= n n_0)
      (= n! n_0)
      (= k k!)
      (= j j!)
    )
    (and
      (= i_27 i)
      (= j_28 j)
      (<= i_27 n_0)
      (= i_21 (+ i_27 1))
      (= j_22 (+ j_28 i_21))
      (= j_22 j!)
      (= i_21 i!)
      (= n n_0)
      (= n! n_0)
      (= k k!)
    )
  )
)

(define-fun post-f ((i Int)(j Int)(k Int)(n Int)(i_19 Int)(i_21 Int)(i_27 Int)(j_20 Int)(j_22 Int)(j_28 Int)(k_0 Int)(n_0 Int)) Bool
  (or
    (not
      (and
        (= i i_27)
        (= j j_28)
        (= k k_0)
        (= n n_0)
      )
    )
    (not
      (and
        (not (<= i_27 n_0))
        (not
          (>
            (+ i_27 (+ j_28 k_0))
            (* 2 n_0)
          )
        )
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f i j k n i_19 i_21 i_27 j_20 j_22 j_28 k_0 n_0 )
    (inv-f i j k n )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f i j k n )
      (trans-f i j k n i! j! k! n! i_19 i_21 i_27 j_20 j_22 j_28 k_0 n_0 )
    )
    (inv-f i! j! k! n! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f i j k n )
    (post-f i j k n i_19 i_21 i_27 j_20 j_22 j_28 k_0 n_0 )
  )
))

