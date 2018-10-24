(set-logic LIA)

(declare-const tmp___0 Int)
(declare-const tmp___0! Int)
(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const n Int)
(declare-const n! Int)
(declare-const c Int)
(declare-const c! Int)

(declare-const n_0 Int)
(declare-const c_42 Int)
(declare-const c_37 Int)
(declare-const c_36 Int)
(declare-const c_32 Int)

(define-fun inv-f((c Int)(n Int)(tmp Int)(tmp___0 Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((c Int)(n Int)(tmp Int)(tmp___0 Int)(c_32 Int)(c_36 Int)(c_37 Int)(c_42 Int)(n_0 Int)) Bool
  (and
    (= n n_0)
    (= c c_32)
    (= c_32 0)
    (> n_0 0)
  )
)

(define-fun trans-f ((c Int)(n Int)(tmp Int)(tmp___0 Int)(c! Int)(n! Int)(tmp! Int)(tmp___0! Int)(c_32 Int)(c_36 Int)(c_37 Int)(c_42 Int)(n_0 Int)) Bool
  (or
    (and
      (= c_42 c)
      (= c_42 c!)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
      (= n n!)
      (= c c!)
    )
    (and
      (= c_42 c)
      (not (= c_42 n_0))
      (= c_42 c!)
      (= n n_0)
      (= n! n_0)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
    )
    (and
      (= c_42 c)
      (= c_42 n_0)
      (= c_37 1)
      (= c_37 c!)
      (= n n_0)
      (= n! n_0)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
    )
    (and
      (= c_42 c)
      (not (not (= c_42 n_0)))
      (= c_42 c!)
      (= n n_0)
      (= n! n_0)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
    )
    (and
      (= c_42 c)
      (not (= c_42 n_0))
      (= c_36 (+ c_42 1))
      (= c_36 c!)
      (= n n_0)
      (= n! n_0)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((c Int)(n Int)(tmp Int)(tmp___0 Int)(c_32 Int)(c_36 Int)(c_37 Int)(c_42 Int)(n_0 Int)) Bool
  (or
    (not
      (and
        (= c c_42)
        (= n n_0)
      )
    )
    (not
      (and
        (not (= c_42 n_0))
        (not (>= c_42 0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f c n tmp tmp___0 c_32 c_36 c_37 c_42 n_0 )
    (inv-f c n tmp tmp___0 )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f c n tmp tmp___0 )
      (trans-f c n tmp tmp___0 c! n! tmp! tmp___0! c_32 c_36 c_37 c_42 n_0 )
    )
    (inv-f c! n! tmp! tmp___0! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f c n tmp tmp___0 )
    (post-f c n tmp tmp___0 c_32 c_36 c_37 c_42 n_0 )
  )
))

