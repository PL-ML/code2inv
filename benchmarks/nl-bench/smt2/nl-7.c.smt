(set-logic LIA)

( declare-const w Int )
( declare-const w! Int )
( declare-const x Int )
( declare-const x! Int )
( declare-const y Int )
( declare-const y! Int )
( declare-const z Int )
( declare-const z! Int )

( declare-const w_0 Int )
( declare-const w_1 Int )
( declare-const w_2 Int )
( declare-const w_3 Int )
( declare-const x_0 Int )
( declare-const y_0 Int )
( declare-const z_0 Int )
( declare-const z_1 Int )
( declare-const z_2 Int )
( declare-const z_3 Int )

( define-fun inv-f( ( w Int )( x Int )( y Int )( z Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( w Int )( x Int )( y Int )( z Int )( w_0 Int )( w_1 Int )( w_2 Int )( w_3 Int )( x_0 Int )( y_0 Int )( z_0 Int )( z_1 Int )( z_2 Int )( z_3 Int ) ) Bool
	( or
		( and
			( = w w_1 )
			( = x x_0 )
			( = y y_0 )
			( = z z_1 )
			( >= x_0 0 )
			( and ( >= x_0 0 ) ( >= y_0 x_0 ) )
			( = z_1 0 )
			( = w_1 0 )
		)
		( and
			( = w w_1 )
			( = x x_0 )
			( = y y_0 )
			( = z z_1 )
			( not ( >= x_0 0 ) )
			( and ( >= x_0 0 ) ( >= y_0 x_0 ) )
			( = z_1 0 )
			( = w_1 0 )
		)
	)
)

( define-fun trans-f ( ( w Int )( x Int )( y Int )( z Int )( w! Int )( x! Int )( y! Int )( z! Int )( w_0 Int )( w_1 Int )( w_2 Int )( w_3 Int )( x_0 Int )( y_0 Int )( z_0 Int )( z_1 Int )( z_2 Int )( z_3 Int ) ) Bool
	( or
		( and
			( = w_2 w )
			( = z_2 z )
			( = w_2 w! )
			( = z_2 z! )
			( = y y_0 )
			( = y! y_0 )
			( = x x! )
			( = z z! )
		)
		( and
			( = w_2 w )
			( = z_2 z )
			( < w_2 y_0 )
			( = z_3 ( + z_2 x_0 ) )
			( = w_3 ( + w_2 1 ) )
			( = w_3 w! )
			( = z_3 z! )
			(= x x_0 )
			(= x! x_0 )
			(= y y_0 )
			(= y! y_0 )
		)
	)
)

( define-fun post-f ( ( w Int )( x Int )( y Int )( z Int )( w_0 Int )( w_1 Int )( w_2 Int )( w_3 Int )( x_0 Int )( y_0 Int )( z_0 Int )( z_1 Int )( z_2 Int )( z_3 Int ) ) Bool
	( or
		( not
			( and
				( = w w_2)
				( = x x_0)
				( = y y_0)
				( = z z_2)
			)
		)
		( not
			( and
				( not ( < w_2 y_0 ) )
				( not ( = z_2 ( * x_0 y_0 ) ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f w x y z w_0 w_1 w_2 w_3 x_0 y_0 z_0 z_1 z_2 z_3  )
		( inv-f w x y z )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f w x y z )
			( trans-f w x y z w! x! y! z! w_0 w_1 w_2 w_3 x_0 y_0 z_0 z_1 z_2 z_3 )
		)
		( inv-f w! x! y! z! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f w x y z  )
		( post-f w x y z w_0 w_1 w_2 w_3 x_0 y_0 z_0 z_1 z_2 z_3 )
	)
))

