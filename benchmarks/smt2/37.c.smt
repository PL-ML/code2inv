(set-logic LIA)

(declare-const tmp___0 Int)
(declare-const tmp___0! Int)
(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const c Int)
(declare-const c! Int)

(declare-const c_42 Int)
(declare-const c_37 Int)
(declare-const c_36 Int)
(declare-const c_33 Int)

(define-fun inv-f((c Int)(tmp Int)(tmp___0 Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((c Int)(tmp Int)(tmp___0 Int)(c_33 Int)(c_36 Int)(c_37 Int)(c_42 Int)) Bool
  (and
    (= c c_33)
    (= c_33 0)
  )
)

(define-fun trans-f ((c Int)(tmp Int)(tmp___0 Int)(c! Int)(tmp! Int)(tmp___0! Int)(c_33 Int)(c_36 Int)(c_37 Int)(c_42 Int)) Bool
  (or
    (and
      (= c_42 c)
      (= c_42 c!)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
      (= c c!)
    )
    (and
      (= c_42 c)
      (not (= c_42 40))
      (= c_42 c!)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
    )
    (and
      (= c_42 c)
      (= c_42 40)
      (= c_37 1)
      (= c_37 c!)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
    )
    (and
      (= c_42 c)
      (not (not (= c_42 40)))
      (= c_42 c!)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
    )
    (and
      (= c_42 c)
      (not (= c_42 40))
      (= c_36 (+ c_42 1))
      (= c_36 c!)
      (= tmp___0 tmp___0!)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((c Int)(tmp Int)(tmp___0 Int)(c_33 Int)(c_36 Int)(c_37 Int)(c_42 Int)) Bool
  (or
    (not (= c c_42))
    (not
      (and
        (< c_42 0)
        (> c_42 40)
        (not (= c_42 40))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f c tmp tmp___0 c_33 c_36 c_37 c_42 )
    (inv-f c tmp tmp___0 )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f c tmp tmp___0 )
      (trans-f c tmp tmp___0 c! tmp! tmp___0! c_33 c_36 c_37 c_42 )
    )
    (inv-f c! tmp! tmp___0! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f c tmp tmp___0 )
    (post-f c tmp tmp___0 c_33 c_36 c_37 c_42 )
  )
))

