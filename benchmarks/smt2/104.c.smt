(set-logic LIA)

( declare-const n Int )
( declare-const n! Int )
( declare-const x Int )
( declare-const x! Int )

( declare-const n_0 Int )
( declare-const x_0 Int )
( declare-const x_1 Int )
( declare-const x_2 Int )
( declare-const x_3 Int )

( define-fun inv-f( ( n Int )( x Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( n Int )( x Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( and
		( = x x_1 )
		( = x_1 0 )
	)
)

( define-fun trans-f ( ( n Int )( x Int )( n! Int )( x! Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( or
		( and
			( = x_2 x )
			( = x_2 x! )
			( = n n_0 )
			( = n! n_0 )
		)
		( and
			( = x_2 x )
			( < x_2 n_0 )
			( = x_3 ( + x_2 1 ) )
			( = x_3 x! )
			(= n n_0 )
			(= n! n_0 )
		)
	)
)

( define-fun post-f ( ( n Int )( x Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( or
		( not
			( and
				( = n n_0 )
				( = x x_2)
			)
		)
		( not
			( and
				( not ( < x_2 n_0 ) )
				( not ( = x_2 n_0 ) )
				( not ( < n_0 0 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f n x n_0 x_0 x_1 x_2 x_3  )
		( inv-f n x )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f n x )
			( trans-f n x n! x! n_0 x_0 x_1 x_2 x_3 )
		)
		( inv-f n! x! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f n x  )
		( post-f n x n_0 x_0 x_1 x_2 x_3 )
	)
))

