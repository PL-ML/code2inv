(set-logic LIA)

(declare-const m Int)
(declare-const m! Int)
(declare-const k Int)
(declare-const k! Int)
(declare-const j Int)
(declare-const j! Int)
(declare-const a Int)
(declare-const a! Int)

(declare-const m_31 Int)
(declare-const m_30 Int)
(declare-const m_23 Int)
(declare-const m_0 Int)
(declare-const k_29 Int)
(declare-const k_24 Int)
(declare-const k_22 Int)
(declare-const j_0 Int)
(declare-const a_0 Int)

(define-fun inv-f((a Int)(j Int)(k Int)(m Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((a Int)(j Int)(k Int)(m Int)(a_0 Int)(j_0 Int)(k_22 Int)(k_24 Int)(k_29 Int)(m_0 Int)(m_23 Int)(m_30 Int)(m_31 Int)) Bool
  (and
    (= m m_0)
    (= k k_22)
    (= j j_0)
    (= a a_0)
    (<= a_0 m_0)
    (< j_0 1)
    (= k_22 0)
  )
)

(define-fun trans-f ((a Int)(j Int)(k Int)(m Int)(a! Int)(j! Int)(k! Int)(m! Int)(a_0 Int)(j_0 Int)(k_22 Int)(k_24 Int)(k_29 Int)(m_0 Int)(m_23 Int)(m_30 Int)(m_31 Int)) Bool
  (or
    (and
      (= k_29 k)
      (= m_30 m)
      (= m_30 m!)
      (= k_29 k!)
      (= m m!)
      (= j j!)
      (= a a!)
    )
    (and
      (= k_29 k)
      (= m_30 m)
      (< k_29 1)
      (not (< m_30 a_0))
      (= m_31 m_30)
      (= k_24 (+ k_29 1))
      (= m_31 m!)
      (= k_24 k!)
      (= a a_0)
      (= a! a_0)
      (= j j!)
    )
    (and
      (= k_29 k)
      (= m_30 m)
      (< k_29 1)
      (< m_30 a_0)
      (= m_23 a_0)
      (= m_31 m_23)
      (= k_24 (+ k_29 1))
      (= m_31 m!)
      (= k_24 k!)
      (= a a_0)
      (= a! a_0)
      (= j j!)
    )
  )
)

(define-fun post-f ((a Int)(j Int)(k Int)(m Int)(a_0 Int)(j_0 Int)(k_22 Int)(k_24 Int)(k_29 Int)(m_0 Int)(m_23 Int)(m_30 Int)(m_31 Int)) Bool
  (or
    (not
      (and
        (= a a_0)
        (= k k_29)
        (= m m_30)
      )
    )
    (not
      (and
        (not (< k_29 1))
        (not (>= a_0 m_30))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f a j k m a_0 j_0 k_22 k_24 k_29 m_0 m_23 m_30 m_31 )
    (inv-f a j k m )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f a j k m )
      (trans-f a j k m a! j! k! m! a_0 j_0 k_22 k_24 k_29 m_0 m_23 m_30 m_31 )
    )
    (inv-f a! j! k! m! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f a j k m )
    (post-f a j k m a_0 j_0 k_22 k_24 k_29 m_0 m_23 m_30 m_31 )
  )
))

