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
(declare-const i_35 Int)
(declare-const i_30 Int)
(declare-const i_25 Int)

(define-fun inv-f((i Int)(tmp Int)(x Int)(y Int)) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

(define-fun pre-f ((i Int)(tmp Int)(x Int)(y Int)(i_25 Int)(i_30 Int)(i_35 Int)(x_0 Int)(y_0 Int)) Bool
  (and
    (= y y_0)
    (= x x_0)
    (= i i_25)
    (= i_25 0)
    (>= x_0 0)
    (>= y_0 0)
    (>= x_0 y_0)
  )
)

(define-fun trans-f ((i Int)(tmp Int)(x Int)(y Int)(i! Int)(tmp! Int)(x! Int)(y! Int)(i_25 Int)(i_30 Int)(i_35 Int)(x_0 Int)(y_0 Int)) Bool
  (or
    (and
      (= i_35 i)
      (= i_35 i!)
      (= y y!)
      (= x x!)
      (= tmp tmp!)
      (= i i!)
    )
    (and
      (= i_35 i)
      (not (< i_35 y_0))
      (= i_35 i!)
      (= y y_0)
      (= y! y_0)
      (= x x!)
      (= tmp tmp!)
    )
    (and
      (= i_35 i)
      (< i_35 y_0)
      (= i_30 (+ i_35 1))
      (= i_30 i!)
      (= y y_0)
      (= y! y_0)
      (= x x!)
      (= tmp tmp!)
    )
  )
)

(define-fun post-f ((i Int)(tmp Int)(x Int)(y Int)(i_25 Int)(i_30 Int)(i_35 Int)(x_0 Int)(y_0 Int)) Bool
  (or
    (not
      (and
        (= i i_35)
        (= x x_0)
        (= y y_0)
      )
    )
    (not
      (and
        (< i_35 y_0)
        (not (< i_35 x_0))
      )
    )
  )
)

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (pre-f i tmp x y i_25 i_30 i_35 x_0 y_0 )
    (inv-f i tmp x y )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (and
      (inv-f i tmp x y )
      (trans-f i tmp x y i! tmp! x! y! i_25 i_30 i_35 x_0 y_0 )
    )
    (inv-f i! tmp! x! y! )
  )
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
(assert (not
  (=>
    (inv-f i tmp x y )
    (post-f i tmp x y i_25 i_30 i_35 x_0 y_0 )
  )
))

