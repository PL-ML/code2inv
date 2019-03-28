(set-logic LIA)

( declare-const x Int )
( declare-const x! Int )
( declare-const y Int )
( declare-const y! Int )
( declare-const z Int )
( declare-const z! Int )

( declare-const x_0 Int )
( declare-const x_1 Int )
( declare-const x_2 Int )
( declare-const y_0 Int )
( declare-const y_1 Int )
( declare-const y_2 Int )
( declare-const y_3 Int )
( declare-const z_0 Int )

( define-fun inv-f( ( x Int )( y Int )( z Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( x Int )( y Int )( z Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( z_0 Int ) ) Bool
	( and
		( = x x_0 )
		( = x_0 0 )
	)
)

( define-fun trans-f ( ( x Int )( y Int )( z Int )( x! Int )( y! Int )( z! Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( z_0 Int ) ) Bool
	( or
		( and
			( = x_1 x )
			( = y_1 y )
			( = x_1 x! )
			( = y_1 y! )
			( = y y! )
			( = z z! )
		)
		( and
			( = x_1 x )
			( = y_1 y )
			( < x_1 500 )
			( = x_2 ( + x_1 1 ) )
			( <= z_0 y_1 )
			( = y_2 z_0 )
			( = y_3 y_2 )
			( = x_2 x! )
			( = y_3 y! )
			(= z z_0 )
			(= z! z_0 )
		)
		( and
			( = x_1 x )
			( = y_1 y )
			( < x_1 500 )
			( = x_2 ( + x_1 1 ) )
			( not ( <= z_0 y_1 ) )
			( = y_3 y_1 )
			( = x_2 x! )
			( = y_3 y! )
			(= z z_0 )
			(= z! z_0 )
		)
	)
)

( define-fun post-f ( ( x Int )( y Int )( z Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( z_0 Int ) ) Bool
	( or
		( not
			( and
				( = x x_1)
				( = y y_1)
				( = z z_0 )
			)
		)
		( not
			( and
				( not ( < x_1 500 ) )
				( not ( >= z_0 y_1 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f x y z x_0 x_1 x_2 y_0 y_1 y_2 y_3 z_0  )
		( inv-f x y z )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f x y z )
			( trans-f x y z x! y! z! x_0 x_1 x_2 y_0 y_1 y_2 y_3 z_0 )
		)
		( inv-f x! y! z! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f x y z  )
		( post-f x y z x_0 x_1 x_2 y_0 y_1 y_2 y_3 z_0 )
	)
))

