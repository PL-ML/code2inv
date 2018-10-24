(set-logic LIA)

(declare-const z Int)
(declare-const z! Int)
(declare-const y Int)
(declare-const y! Int)
(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const c Int)
(declare-const c! Int)

(declare-const z_41 Int)
(declare-const z_33 Int)
(declare-const z_31 Int)
(declare-const y_0 Int)
(declare-const c_39 Int)
(declare-const c_34 Int)
(declare-const c_28 Int)

(define-fun inv-f((c Int)(tmp Int)(y Int)(z Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((c Int)(tmp Int)(y Int)(z Int)(c_28 Int)(c_34 Int)(c_39 Int)(y_0 Int)(z_31 Int)(z_33 Int)(z_41 Int)) Bool
  (and
    (= z z_31)
    (= y y_0)
    (= c c_28)
    (= c_28 0)
    (>= y_0 0)
    (>= y_0 127)
    (= z_31 (* 36 y_0))
  )
)

(define-fun trans-f ((c Int)(tmp Int)(y Int)(z Int)(c! Int)(tmp! Int)(y! Int)(z! Int)(c_28 Int)(c_34 Int)(c_39 Int)(y_0 Int)(z_31 Int)(z_33 Int)(z_41 Int)) Bool
  (or
    (and
      (= c_39 c)
      (= z_41 z)
      (= z_41 z!)
      (= c_39 c!)
      (= z z!)
      (= y y!)
      (= tmp tmp!)
      (= c c!)
    )
    (and
      (= c_39 c)
      (= z_41 z)
      (not (< c_39 36))
      (= z_41 z!)
      (= c_39 c!)
      (= z z!)
      (= y y!)
      (= tmp tmp!)
    )
    (and
      (= c_39 c)
      (= z_41 z)
      (< c_39 36)
      (= z_33 (+ z_41 1))
      (= c_34 (+ c_39 1))
      (= z_33 z!)
      (= c_34 c!)
      (= y y!)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((c Int)(tmp Int)(y Int)(z Int)(c_28 Int)(c_34 Int)(c_39 Int)(y_0 Int)(z_31 Int)(z_33 Int)(z_41 Int)) Bool
  (or
    (not
      (and
        (= c c_39)
        (= z z_41)
      )
    )
    (not
      (and
        (< z_41 0)
        (>= z_41 4608)
        (not (>= c_39 36))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f c tmp y z c_28 c_34 c_39 y_0 z_31 z_33 z_41 )
    (inv-f c tmp y z )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f c tmp y z )
      (trans-f c tmp y z c! tmp! y! z! c_28 c_34 c_39 y_0 z_31 z_33 z_41 )
    )
    (inv-f c! tmp! y! z! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f c tmp y z )
    (post-f c tmp y z c_28 c_34 c_39 y_0 z_31 z_33 z_41 )
  )
))

