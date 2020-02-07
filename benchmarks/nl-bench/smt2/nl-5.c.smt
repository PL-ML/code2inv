(set-logic LIA)

( declare-const w Int )
( declare-const w! Int )
( declare-const x Int )
( declare-const x! Int )
( declare-const z Int )
( declare-const z! Int )
( declare-const tmp Int )
( declare-const tmp! Int )

( declare-const w_0 Int )
( declare-const w_1 Int )
( declare-const w_2 Int )
( declare-const x_0 Int )
( declare-const z_0 Int )
( declare-const z_1 Int )
( declare-const z_2 Int )
( declare-const z_3 Int )

( define-fun inv-f( ( w Int )( x Int )( z Int )( tmp Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( w Int )( x Int )( z Int )( tmp Int )( w_0 Int )( w_1 Int )( w_2 Int )( x_0 Int )( z_0 Int )( z_1 Int )( z_2 Int )( z_3 Int ) ) Bool
	( and
		( = w w_0 )
		( = x x_0 )
		( = z z_1 )
		( = z_1 ( * w_0 x_0 ) )
	)
)

( define-fun trans-f ( ( w Int )( x Int )( z Int )( tmp Int )( w! Int )( x! Int )( z! Int )( tmp! Int )( w_0 Int )( w_1 Int )( w_2 Int )( x_0 Int )( z_0 Int )( z_1 Int )( z_2 Int )( z_3 Int ) ) Bool
	( or
		( and
			( = w_1 w )
			( = z_2 z )
			( = w_1 w! )
			( = z_2 z! )
			( = w w! )
			( = x x! )
			( = z z! )
			(= tmp tmp! )
		)
		( and
			( = w_1 w )
			( = z_2 z )
			( = w_2 ( * w_1 x_0 ) )
			( = z_3 ( * z_2 x_0 ) )
			( = w_2 w! )
			( = z_3 z! )
			(= x x_0 )
			(= x! x_0 )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( w Int )( x Int )( z Int )( tmp Int )( w_0 Int )( w_1 Int )( w_2 Int )( x_0 Int )( z_0 Int )( z_1 Int )( z_2 Int )( z_3 Int ) ) Bool
	( or
		( not
			( and
				( = w w_1)
				( = x x_0)
				( = z z_2)
			)
		)
		( not
			( and
				( not ( = z_2 ( * w_1 x_0 ) ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f w x z tmp w_0 w_1 w_2 x_0 z_0 z_1 z_2 z_3  )
		( inv-f w x z tmp )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f w x z tmp )
			( trans-f w x z tmp w! x! z! tmp! w_0 w_1 w_2 x_0 z_0 z_1 z_2 z_3 )
		)
		( inv-f w! x! z! tmp! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f w x z tmp  )
		( post-f w x z tmp w_0 w_1 w_2 x_0 z_0 z_1 z_2 z_3 )
	)
))

