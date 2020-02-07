(set-logic LIA)

( declare-const x Int )
( declare-const x! Int )
( declare-const y Int )
( declare-const y! Int )
( declare-const tmp Int )
( declare-const tmp! Int )

( declare-const x_0 Int )
( declare-const x_1 Int )
( declare-const x_2 Int )
( declare-const y_0 Int )
( declare-const y_1 Int )
( declare-const y_2 Int )

( define-fun inv-f( ( x Int )( y Int )( tmp Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( x Int )( y Int )( tmp Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( and
		( = x x_0 )
		( = y y_0 )
		( >= x_0 0 )
		( <= x_0 10 )
		( <= y_0 10 )
		( >= y_0 0 )
	)
)

( define-fun trans-f ( ( x Int )( y Int )( tmp Int )( x! Int )( y! Int )( tmp! Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( or
		( and
			( = x_1 x )
			( = y_1 y )
			( = x_1 x! )
			( = y_1 y! )
			( = x x! )
			( = y y! )
			(= tmp tmp! )
		)
		( and
			( = x_1 x )
			( = y_1 y )
			( = x_2 ( + x_1 10 ) )
			( = y_2 ( + y_1 10 ) )
			( = x_2 x! )
			( = y_2 y! )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( x Int )( y Int )( tmp Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( or
		( not
			( and
				( = x x_1)
				( = y y_1)
			)
		)
		( not
			( and
				( = y_1 0 )
				( not ( not ( = x_1 20 ) ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f x y tmp x_0 x_1 x_2 y_0 y_1 y_2  )
		( inv-f x y tmp )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f x y tmp )
			( trans-f x y tmp x! y! tmp! x_0 x_1 x_2 y_0 y_1 y_2 )
		)
		( inv-f x! y! tmp! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f x y tmp  )
		( post-f x y tmp x_0 x_1 x_2 y_0 y_1 y_2 )
	)
))

