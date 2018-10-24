(set-logic LIA)

(declare-const y Int)
(declare-const y! Int)
(declare-const x Int)
(declare-const x! Int)
(declare-const tmp Int)
(declare-const tmp! Int)
(declare-const i Int)
(declare-const i! Int)

(declare-const y_0 Int)
(declare-const x_0 Int)
(declare-const i_38 Int)
(declare-const i_33 Int)
(declare-const i_28 Int)

(define-fun inv-f((i Int)(tmp Int)(x Int)(y Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((i Int)(tmp Int)(x Int)(y Int)(i_28 Int)(i_33 Int)(i_38 Int)(x_0 Int)(y_0 Int)) Bool
  (and
    (= y y_0)
    (= x x_0)
    (= i i_28)
    (= i_28 0)
    (>= x_0 0)
    (>= y_0 0)
    (>= x_0 y_0)
  )
)

(define-fun trans-f ((i Int)(tmp Int)(x Int)(y Int)(i! Int)(tmp! Int)(x! Int)(y! Int)(i_28 Int)(i_33 Int)(i_38 Int)(x_0 Int)(y_0 Int)) Bool
  (or
    (and
      (= i_38 i)
      (= i_38 i!)
      (= y y!)
      (= x x!)
      (= tmp tmp!)
      (= i i!)
    )
    (and
      (= i_38 i)
      (not (< i_38 y_0))
      (= i_38 i!)
      (= y y_0)
      (= y! y_0)
      (= x x!)
      (= tmp tmp!)
    )
    (and
      (= i_38 i)
      (< i_38 y_0)
      (= i_33 (+ i_38 1))
      (= i_33 i!)
      (= y y_0)
      (= y! y_0)
      (= x x!)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((i Int)(tmp Int)(x Int)(y Int)(i_28 Int)(i_33 Int)(i_38 Int)(x_0 Int)(y_0 Int)) Bool
  (or
    (not
      (and
        (= i i_38)
        (= x x_0)
        (= y y_0)
      )
    )
    (not
      (and
        (>= i_38 x_0)
        (> 0 i_38)
        (not (>= i_38 y_0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f i tmp x y i_28 i_33 i_38 x_0 y_0 )
    (inv-f i tmp x y )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f i tmp x y )
      (trans-f i tmp x y i! tmp! x! y! i_28 i_33 i_38 x_0 y_0 )
    )
    (inv-f i! tmp! x! y! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f i tmp x y )
    (post-f i tmp x y i_28 i_33 i_38 x_0 y_0 )
  )
))

