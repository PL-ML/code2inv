(set-logic LIA)

(declare-const m Int)
(declare-const m! Int)
(declare-const k Int)
(declare-const k! Int)
(declare-const j Int)
(declare-const j! Int)
(declare-const c Int)
(declare-const c! Int)
(declare-const a Int)
(declare-const a! Int)

(declare-const m_31 Int)
(declare-const m_30 Int)
(declare-const m_23 Int)
(declare-const m_0 Int)
(declare-const k_29 Int)
(declare-const k_24 Int)
(declare-const k_22 Int)
(declare-const j_21 Int)
(declare-const c_0 Int)
(declare-const a_0 Int)

(define-fun inv-f((a Int)(c Int)(j Int)(k Int)(m Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((a Int)(c Int)(j Int)(k Int)(m Int)(a_0 Int)(c_0 Int)(j_21 Int)(k_22 Int)(k_24 Int)(k_29 Int)(m_0 Int)(m_23 Int)(m_30 Int)(m_31 Int)) Bool
  (and
    (= m m_0)
    (= k k_22)
    (= j j_21)
    (= a a_0)
    (<= a_0 m_0)
    (= j_21 0)
    (= k_22 0)
  )
)

(define-fun trans-f ((a Int)(c Int)(j Int)(k Int)(m Int)(a! Int)(c! Int)(j! Int)(k! Int)(m! Int)(a_0 Int)(c_0 Int)(j_21 Int)(k_22 Int)(k_24 Int)(k_29 Int)(m_0 Int)(m_23 Int)(m_30 Int)(m_31 Int)) Bool
  (or
    (and
      (= k_29 k)
      (= m_30 m)
      (= m_30 m!)
      (= k_29 k!)
      (= c c_0)
      (= c! c_0)
      (= m m!)
      (= j j!)
      (= a a!)
    )
    (and
      (= k_29 k)
      (= m_30 m)
      (< k_29 c_0)
      (not (< m_30 a_0))
      (= m_31 m_30)
      (= k_24 (+ k_29 1))
      (= m_31 m!)
      (= k_24 k!)
      (= a a_0)
      (= a! a_0)
      (= c c_0)
      (= c! c_0)
      (= j j!)
    )
    (and
      (= k_29 k)
      (= m_30 m)
      (< k_29 c_0)
      (< m_30 a_0)
      (= m_23 a_0)
      (= m_31 m_23)
      (= k_24 (+ k_29 1))
      (= m_31 m!)
      (= k_24 k!)
      (= a a_0)
      (= a! a_0)
      (= c c_0)
      (= c! c_0)
      (= j j!)
    )
  )
)

(define-fun post-f ((a Int)(c Int)(j Int)(k Int)(m Int)(a_0 Int)(c_0 Int)(j_21 Int)(k_22 Int)(k_24 Int)(k_29 Int)(m_0 Int)(m_23 Int)(m_30 Int)(m_31 Int)) Bool
  (or
    (not
      (and
        (= a a_0)
        (= c c_0)
        (= k k_29)
        (= m m_30)
      )
    )
    (not
      (and
        (not (< k_29 c_0))
        (not (<= a_0 m_30))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f a c j k m a_0 c_0 j_21 k_22 k_24 k_29 m_0 m_23 m_30 m_31 )
    (inv-f a c j k m )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f a c j k m )
      (trans-f a c j k m a! c! j! k! m! a_0 c_0 j_21 k_22 k_24 k_29 m_0 m_23 m_30 m_31 )
    )
    (inv-f a! c! j! k! m! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f a c j k m )
    (post-f a c j k m a_0 c_0 j_21 k_22 k_24 k_29 m_0 m_23 m_30 m_31 )
  )
))

