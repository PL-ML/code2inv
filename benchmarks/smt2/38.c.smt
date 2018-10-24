(set-logic LIA)

(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const n Int)
(declare-const n! Int)
(declare-const c Int)
(declare-const c! Int)

(declare-const n_0 Int)
(declare-const c_33 Int)
(declare-const c_28 Int)
(declare-const c_27 Int)
(declare-const c_24 Int)

(define-fun inv-f((c Int)(n Int)(tmp Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((c Int)(n Int)(tmp Int)(c_24 Int)(c_27 Int)(c_28 Int)(c_33 Int)(n_0 Int)) Bool
  (and
    (= n n_0)
    (= c c_24)
    (= c_24 0)
    (> n_0 0)
  )
)

(define-fun trans-f ((c Int)(n Int)(tmp Int)(c! Int)(n! Int)(tmp! Int)(c_24 Int)(c_27 Int)(c_28 Int)(c_33 Int)(n_0 Int)) Bool
  (or
    (and
      (= c_33 c)
      (= c_33 c!)
      (= tmp tmp!)
      (= n n!)
      (= c c!)
    )
    (and
      (= c_33 c)
      (not (= c_33 n_0))
      (= c_28 (+ c_33 1))
      (= c_28 c!)
      (= n n_0)
      (= n! n_0)
      (= tmp tmp!)
    )
    (and
      (= c_33 c)
      (= c_33 n_0)
      (= c_27 1)
      (= c_27 c!)
      (= n n_0)
      (= n! n_0)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((c Int)(n Int)(tmp Int)(c_24 Int)(c_27 Int)(c_28 Int)(c_33 Int)(n_0 Int)) Bool
  (or
    (not
      (and
        (= c c_33)
        (= n n_0)
      )
    )
    (not
      (and
        (= c_33 n_0)
        (not (>= c_33 0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f c n tmp c_24 c_27 c_28 c_33 n_0 )
    (inv-f c n tmp )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f c n tmp )
      (trans-f c n tmp c! n! tmp! c_24 c_27 c_28 c_33 n_0 )
    )
    (inv-f c! n! tmp! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f c n tmp )
    (post-f c n tmp c_24 c_27 c_28 c_33 n_0 )
  )
))

