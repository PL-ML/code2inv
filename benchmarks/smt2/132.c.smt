(set-logic LIA)

(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const t Int)
(declare-const t! Int)
(declare-const j Int)
(declare-const j! Int)
(declare-const i Int)
(declare-const i! Int)
(declare-const c Int)
(declare-const c! Int)

(declare-const t_32 Int)
(declare-const t_24 Int)
(declare-const t_0 Int)
(declare-const j_31 Int)
(declare-const j_23 Int)
(declare-const j_0 Int)
(declare-const i_30 Int)
(declare-const i_25 Int)
(declare-const i_21 Int)
(declare-const c_0 Int)

(define-fun inv-f((c Int)(i Int)(j Int)(t Int)(tmp Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((c Int)(i Int)(j Int)(t Int)(tmp Int)(c_0 Int)(i_21 Int)(i_25 Int)(i_30 Int)(j_0 Int)(j_23 Int)(j_31 Int)(t_0 Int)(t_24 Int)(t_32 Int)) Bool
  (and
    (= i i_21)
    (= i_21 0)
  )
)

(define-fun trans-f ((c Int)(i Int)(j Int)(t Int)(tmp Int)(c! Int)(i! Int)(j! Int)(t! Int)(tmp! Int)(c_0 Int)(i_21 Int)(i_25 Int)(i_30 Int)(j_0 Int)(j_23 Int)(j_31 Int)(t_0 Int)(t_24 Int)(t_32 Int)) Bool
  (or
    (and
      (= i_30 i)
      (= j_31 j)
      (= t_32 t)
      (= t_32 t!)
      (= j_31 j!)
      (= i_30 i!)
      (= tmp tmp!)
      (= t t!)
      (= j j!)
      (= i i!)
      (= c c!)
    )
    (and
      (= i_30 i)
      (= j_31 j)
      (= t_32 t)
      (not (> c_0 48))
      (= t_32 t!)
      (= j_31 j!)
      (= i_30 i!)
      (= c c_0)
      (= c! c_0)
      (= tmp tmp!)
      (= t t!)
      (= j j!)
      (= i i!)
    )
    (and
      (= i_30 i)
      (= j_31 j)
      (= t_32 t)
      (> c_0 48)
      (not (< c_0 57))
      (= t_32 t!)
      (= j_31 j!)
      (= i_30 i!)
      (= c c_0)
      (= c! c_0)
      (= tmp tmp!)
      (= t t!)
      (= j j!)
      (= i i!)
    )
    (and
      (= i_30 i)
      (= j_31 j)
      (= t_32 t)
      (> c_0 48)
      (< c_0 57)
      (= j_23 (+ i_30 i_30))
      (= t_24 (- c_0 48))
      (= i_25 (+ j_23 t_24))
      (= t_24 t!)
      (= j_23 j!)
      (= i_25 i!)
      (= c c_0)
      (= c! c_0)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((c Int)(i Int)(j Int)(t Int)(tmp Int)(c_0 Int)(i_21 Int)(i_25 Int)(i_30 Int)(j_0 Int)(j_23 Int)(j_31 Int)(t_0 Int)(t_24 Int)(t_32 Int)) Bool
  (or
    (not (= i i_30))
    (not (not (>= i_30 0)))
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f c i j t tmp c_0 i_21 i_25 i_30 j_0 j_23 j_31 t_0 t_24 t_32 )
    (inv-f c i j t tmp )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f c i j t tmp )
      (trans-f c i j t tmp c! i! j! t! tmp! c_0 i_21 i_25 i_30 j_0 j_23 j_31 t_0 t_24 t_32 )
    )
    (inv-f c! i! j! t! tmp! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f c i j t tmp )
    (post-f c i j t tmp c_0 i_21 i_25 i_30 j_0 j_23 j_31 t_0 t_24 t_32 )
  )
))

