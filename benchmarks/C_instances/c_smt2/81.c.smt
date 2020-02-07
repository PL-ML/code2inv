(set-logic LIA)

( declare-const i Int )
( declare-const i! Int )
( declare-const x Int )
( declare-const x! Int )
( declare-const y Int )
( declare-const y! Int )
( declare-const tmp Int )
( declare-const tmp! Int )

( declare-const i_0 Int )
( declare-const i_1 Int )
( declare-const i_2 Int )
( declare-const i_3 Int )
( declare-const i_4 Int )
( declare-const x_0 Int )
( declare-const y_0 Int )

( define-fun inv-f( ( i Int )( x Int )( y Int )( tmp Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( i Int )( x Int )( y Int )( tmp Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( i_4 Int )( x_0 Int )( y_0 Int ) ) Bool
	( and
		( = i i_1 )
		( = x x_0 )
		( = y y_0 )
		( = i_1 0 )
		( >= x_0 0 )
		( >= y_0 0 )
		( >= x_0 y_0 )
	)
)

( define-fun trans-f ( ( i Int )( x Int )( y Int )( tmp Int )( i! Int )( x! Int )( y! Int )( tmp! Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( i_4 Int )( x_0 Int )( y_0 Int ) ) Bool
	( or
		( and
			( = i_2 i )
			( = i_2 i! )
			( = i i! )
			( = x x! )
			( = y y! )
			(= tmp tmp! )
		)
		( and
			( = i_2 i )
			( < i_2 y_0 )
			( = i_3 ( + i_2 1 ) )
			( = i_4 i_3 )
			( = i_4 i! )
			(= x x_0 )
			(= x! x_0 )
			(= y y_0 )
			(= y! y_0 )
			(= tmp tmp! )
		)
		( and
			( = i_2 i )
			( not ( < i_2 y_0 ) )
			( = i_4 i_2 )
			( = i_4 i! )
			(= x x_0 )
			(= x! x_0 )
			(= y y_0 )
			(= y! y_0 )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( i Int )( x Int )( y Int )( tmp Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( i_4 Int )( x_0 Int )( y_0 Int ) ) Bool
	( or
		( not
			( and
				( = i i_2)
				( = x x_0)
				( = y y_0)
			)
		)
		( not
			( and
				( < i_2 y_0 )
				( not ( <= 0 i_2 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f i x y tmp i_0 i_1 i_2 i_3 i_4 x_0 y_0  )
		( inv-f i x y tmp )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f i x y tmp )
			( trans-f i x y tmp i! x! y! tmp! i_0 i_1 i_2 i_3 i_4 x_0 y_0 )
		)
		( inv-f i! x! y! tmp! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f i x y tmp  )
		( post-f i x y tmp i_0 i_1 i_2 i_3 i_4 x_0 y_0 )
	)
))

