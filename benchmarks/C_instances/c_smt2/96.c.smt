(set-logic LIA)

( declare-const i Int )
( declare-const i! Int )
( declare-const j Int )
( declare-const j! Int )
( declare-const x Int )
( declare-const x! Int )
( declare-const y Int )
( declare-const y! Int )

( declare-const i_0 Int )
( declare-const i_1 Int )
( declare-const i_2 Int )
( declare-const i_3 Int )
( declare-const j_0 Int )
( declare-const j_1 Int )
( declare-const j_2 Int )
( declare-const j_3 Int )
( declare-const x_0 Int )
( declare-const y_0 Int )
( declare-const y_1 Int )

( define-fun inv-f( ( i Int )( j Int )( x Int )( y Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( i Int )( j Int )( x Int )( y Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( x_0 Int )( y_0 Int )( y_1 Int ) ) Bool
	( and
		( = i i_1 )
		( = j j_1 )
		( = y y_1 )
		( = j_1 0 )
		( = i_1 0 )
		( = y_1 1 )
	)
)

( define-fun trans-f ( ( i Int )( j Int )( x Int )( y Int )( i! Int )( j! Int )( x! Int )( y! Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( x_0 Int )( y_0 Int )( y_1 Int ) ) Bool
	( or
		( and
			( = i_2 i )
			( = j_2 j )
			( = i_2 i! )
			( = j_2 j! )
			( = x x_0 )
			( = x! x_0 )
			( = j j! )
			( = y y! )
		)
		( and
			( = i_2 i )
			( = j_2 j )
			( <= i_2 x_0 )
			( = i_3 ( + i_2 1 ) )
			( = j_3 ( + j_2 y_1 ) )
			( = i_3 i! )
			( = j_3 j! )
			(= x x_0 )
			(= x! x_0 )
			(= y y_1 )
			(= y! y_1 )
		)
	)
)

( define-fun post-f ( ( i Int )( j Int )( x Int )( y Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( x_0 Int )( y_0 Int )( y_1 Int ) ) Bool
	( or
		( not
			( and
				( = i i_2)
				( = j j_2)
				( = x x_0 )
				( = y y_1)
			)
		)
		( not
			( and
				( not ( <= i_2 x_0 ) )
				( not ( = i_2 j_2 ) )
				( not ( not ( = y_1 1 ) ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f i j x y i_0 i_1 i_2 i_3 j_0 j_1 j_2 j_3 x_0 y_0 y_1  )
		( inv-f i j x y )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f i j x y )
			( trans-f i j x y i! j! x! y! i_0 i_1 i_2 i_3 j_0 j_1 j_2 j_3 x_0 y_0 y_1 )
		)
		( inv-f i! j! x! y! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f i j x y  )
		( post-f i j x y i_0 i_1 i_2 i_3 j_0 j_1 j_2 j_3 x_0 y_0 y_1 )
	)
))

