(set-logic LIA)

(declare-const z Int)
(declare-const z! Int)
(declare-const y Int)
(declare-const y! Int)
(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const c Int)
(declare-const c! Int)

(declare-const z_38 Int)
(declare-const z_30 Int)
(declare-const z_28 Int)
(declare-const y_0 Int)
(declare-const c_36 Int)
(declare-const c_31 Int)
(declare-const c_25 Int)

(define-fun inv-f((c Int)(tmp Int)(y Int)(z Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((c Int)(tmp Int)(y Int)(z Int)(c_25 Int)(c_31 Int)(c_36 Int)(y_0 Int)(z_28 Int)(z_30 Int)(z_38 Int)) Bool
  (and
    (= z z_28)
    (= y y_0)
    (= c c_25)
    (= c_25 0)
    (>= y_0 0)
    (>= y_0 127)
    (= z_28 (* 36 y_0))
  )
)

(define-fun trans-f ((c Int)(tmp Int)(y Int)(z Int)(c! Int)(tmp! Int)(y! Int)(z! Int)(c_25 Int)(c_31 Int)(c_36 Int)(y_0 Int)(z_28 Int)(z_30 Int)(z_38 Int)) Bool
  (or
    (and
      (= c_36 c)
      (= z_38 z)
      (= z_38 z!)
      (= c_36 c!)
      (= z z!)
      (= y y!)
      (= tmp tmp!)
      (= c c!)
    )
    (and
      (= c_36 c)
      (= z_38 z)
      (not (< c_36 36))
      (= z_38 z!)
      (= c_36 c!)
      (= z z!)
      (= y y!)
      (= tmp tmp!)
    )
    (and
      (= c_36 c)
      (= z_38 z)
      (< c_36 36)
      (= z_30 (+ z_38 1))
      (= c_31 (+ c_36 1))
      (= z_30 z!)
      (= c_31 c!)
      (= y y!)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((c Int)(tmp Int)(y Int)(z Int)(c_25 Int)(c_31 Int)(c_36 Int)(y_0 Int)(z_28 Int)(z_30 Int)(z_38 Int)) Bool
  (or
    (not
      (and
        (= c c_36)
        (= z z_38)
      )
    )
    (not
      (and
        (< c_36 36)
        (not (>= z_38 0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f c tmp y z c_25 c_31 c_36 y_0 z_28 z_30 z_38 )
    (inv-f c tmp y z )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f c tmp y z )
      (trans-f c tmp y z c! tmp! y! z! c_25 c_31 c_36 y_0 z_28 z_30 z_38 )
    )
    (inv-f c! tmp! y! z! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f c tmp y z )
    (post-f c tmp y z c_25 c_31 c_36 y_0 z_28 z_30 z_38 )
  )
))

