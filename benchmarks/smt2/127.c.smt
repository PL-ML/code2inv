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
( declare-const j_0 Int )
( declare-const j_1 Int )
( declare-const x_0 Int )
( declare-const x_1 Int )
( declare-const x_2 Int )
( declare-const y_0 Int )
( declare-const y_1 Int )
( declare-const y_2 Int )

( define-fun inv-f( ( i Int )( j Int )( x Int )( y Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( i Int )( j Int )( x Int )( y Int )( i_0 Int )( i_1 Int )( j_0 Int )( j_1 Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( and
		( = i i_1 )
		( = j j_1 )
		( = x x_0 )
		( = y y_0 )
		( = i_1 x_0 )
		( = j_1 y_0 )
	)
)

( define-fun trans-f ( ( i Int )( j Int )( x Int )( y Int )( i! Int )( j! Int )( x! Int )( y! Int )( i_0 Int )( i_1 Int )( j_0 Int )( j_1 Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( or
		( and
			( = x_1 x )
			( = y_1 y )
			( = x_1 x! )
			( = y_1 y! )
			( = i i! )
			( = j j! )
			( = y y! )
		)
		( and
			( = x_1 x )
			( = y_1 y )
			( not ( = x_1 0 ) )
			( = x_2 ( - x_1 1 ) )
			( = y_2 ( - y_1 1 ) )
			( = x_2 x! )
			( = y_2 y! )
			(= i i_1 )
			(= i! i_1 )
			(= j j_1 )
			(= j! j_1 )
		)
	)
)

( define-fun post-f ( ( i Int )( j Int )( x Int )( y Int )( i_0 Int )( i_1 Int )( j_0 Int )( j_1 Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( or
		( not
			( and
				( = i i_1)
				( = j j_1)
				( = x x_1)
				( = y y_1)
			)
		)
		( not
			( and
				( not ( not ( = x_1 0 ) ) )
				( not ( = y_1 0 ) )
				( not ( not ( = i_1 j_1 ) ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f i j x y i_0 i_1 j_0 j_1 x_0 x_1 x_2 y_0 y_1 y_2  )
		( inv-f i j x y )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f i j x y )
			( trans-f i j x y i! j! x! y! i_0 i_1 j_0 j_1 x_0 x_1 x_2 y_0 y_1 y_2 )
		)
		( inv-f i! j! x! y! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f i j x y  )
		( post-f i j x y i_0 i_1 j_0 j_1 x_0 x_1 x_2 y_0 y_1 y_2 )
	)
))

