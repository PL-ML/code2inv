(set-logic LIA)

( declare-const x Int )
( declare-const x! Int )

( declare-const x_0 Int )
( declare-const x_1 Int )
( declare-const x_2 Int )
( declare-const x_3 Int )

( define-fun inv-f( ( x Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( x Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( and
		( = x x_1 )
		( = x_1 10000 )
	)
)

( define-fun trans-f ( ( x Int )( x! Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( or
		( and
			( = x_2 x )
			( = x_2 x! )
		)
		( and
			( = x_2 x )
			( > x_2 0 )
			( = x_3 ( - x_2 1 ) )
			( = x_3 x! )
		)
	)
)

( define-fun post-f ( ( x Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( or
		( not
			( = x x_2)
		)
		( not
			( and
				( not ( > x_2 0 ) )
				( not ( = x_2 0 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f x x_0 x_1 x_2 x_3  )
		( inv-f x )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f x )
			( trans-f x x! x_0 x_1 x_2 x_3 )
		)
		( inv-f x! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f x  )
		( post-f x x_0 x_1 x_2 x_3 )
	)
))

