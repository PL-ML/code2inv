(set-logic LIA)

( declare-const n Int )
( declare-const n! Int )
( declare-const x Int )
( declare-const x! Int )
( declare-const y Int )
( declare-const y! Int )

( declare-const n_0 Int )
( declare-const x_0 Int )
( declare-const x_1 Int )
( declare-const x_2 Int )
( declare-const x_3 Int )
( declare-const y_0 Int )
( declare-const y_1 Int )
( declare-const y_2 Int )
( declare-const y_3 Int )

( define-fun inv-f( ( n Int )( x Int )( y Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( n Int )( x Int )( y Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( and
		( = n n_0 )
		( = x x_1 )
		( = y y_1 )
		( >= n_0 0 )
		( = x_1 n_0 )
		( = y_1 0 )
	)
)

( define-fun trans-f ( ( n Int )( x Int )( y Int )( n! Int )( x! Int )( y! Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( or
		( and
			( = x_2 x )
			( = y_2 y )
			( = x_2 x! )
			( = y_2 y! )
			( = n n! )
			( = y y! )
		)
		( and
			( = x_2 x )
			( = y_2 y )
			( > x_2 0 )
			( = y_3 ( + y_2 1 ) )
			( = x_3 ( - x_2 1 ) )
			( = x_3 x! )
			( = y_3 y! )
			(= n n_0 )
			(= n! n_0 )
		)
	)
)

( define-fun post-f ( ( n Int )( x Int )( y Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( or
		( not
			( and
				( = n n_0)
				( = x x_2)
				( = y y_2)
			)
		)
		( not
			( and
				( not ( > x_2 0 ) )
				( not ( = y_2 n_0 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f n x y n_0 x_0 x_1 x_2 x_3 y_0 y_1 y_2 y_3  )
		( inv-f n x y )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f n x y )
			( trans-f n x y n! x! y! n_0 x_0 x_1 x_2 x_3 y_0 y_1 y_2 y_3 )
		)
		( inv-f n! x! y! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f n x y  )
		( post-f n x y n_0 x_0 x_1 x_2 x_3 y_0 y_1 y_2 y_3 )
	)
))

