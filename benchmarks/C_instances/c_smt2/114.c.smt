(set-logic LIA)

( declare-const sn Int )
( declare-const sn! Int )
( declare-const x Int )
( declare-const x! Int )
( declare-const tmp Int )
( declare-const tmp! Int )

( declare-const sn_0 Int )
( declare-const sn_1 Int )
( declare-const sn_2 Int )
( declare-const sn_3 Int )
( declare-const x_0 Int )
( declare-const x_1 Int )
( declare-const x_2 Int )
( declare-const x_3 Int )

( define-fun inv-f( ( sn Int )( x Int )( tmp Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( sn Int )( x Int )( tmp Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( and
		( = sn sn_1 )
		( = x x_1 )
		( = sn_1 0 )
		( = x_1 0 )
	)
)

( define-fun trans-f ( ( sn Int )( x Int )( tmp Int )( sn! Int )( x! Int )( tmp! Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( or
		( and
			( = sn_2 sn )
			( = x_2 x )
			( = sn_2 sn! )
			( = x_2 x! )
			( = sn sn! )
			( = x x! )
			(= tmp tmp! )
		)
		( and
			( = sn_2 sn )
			( = x_2 x )
			( = x_3 ( + x_2 1 ) )
			( = sn_3 ( + sn_2 1 ) )
			( = sn_3 sn! )
			( = x_3 x! )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( sn Int )( x Int )( tmp Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int ) ) Bool
	( or
		( not
			( and
				( = sn sn_2)
				( = x x_2)
			)
		)
		( not
			( and
				( not ( = sn_2 x_2 ) )
				( not ( = sn_2 -1 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f sn x tmp sn_0 sn_1 sn_2 sn_3 x_0 x_1 x_2 x_3  )
		( inv-f sn x tmp )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f sn x tmp )
			( trans-f sn x tmp sn! x! tmp! sn_0 sn_1 sn_2 sn_3 x_0 x_1 x_2 x_3 )
		)
		( inv-f sn! x! tmp! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f sn x tmp  )
		( post-f sn x tmp sn_0 sn_1 sn_2 sn_3 x_0 x_1 x_2 x_3 )
	)
))

